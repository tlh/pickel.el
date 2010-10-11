;;; pickel.el --- elisp object serialization

;; Copyright (C) 2010 tlh <thunkout@gmail.com>

;; File:      pickel.el
;; Author:    tlh <thunkout@gmail.com>
;; Created:   2010-09-29
;; Version:   1.0
;; Keywords:  object serialization
;;
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2 of
;; the License, or (at your option) any later version.
;;
;; This program is distributed in the hope that it will be
;; useful, but WITHOUT ANY WARRANTY; without even the implied
;; warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
;; PURPOSE.  See the GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public
;; License along with this program; if not, write to the Free
;; Software Foundation, Inc., 59 Temple Place, Suite 330, Boston,
;; MA 02111-1307 USA
;;

;;; Commentary:
;;
;;  pickel is an elisp object serialization package.  It can serialize
;;  and deserialize most elisp objects, including any combination of
;;  lists (conses and nil), vectors, hash-tables, strings, integers,
;;  floats, symbols and structs (vectors).  It can't serialize
;;  functions, subrs (subroutines) or opaque C types like
;;  window-configurations.
;;
;;  `pickel' works by printing to a stream a representation of the
;;  object on which it's called.  This representation can be used by
;;  `unpickel' to reconstruct the object.  The unpickeled object isn't
;;  `eq' to the original, although the two are "equal" in the spirit
;;  of `equal', in the sense that their structure and content are
;;  `equal':
;;
;;    (setq foo (pickel-to-string '(bar baz)))
;;
;;    => "( ... pickeled foo here ... )"
;;
;;    (equal (unpickel-string foo) '(bar baz))
;;
;;    => t
;;
;;    (eq (unpickel-string foo) '(bar baz))
;;
;;    => nil
;;
;;  pickel correctly reconstructs cycles in the object graph.  Take
;;  for instance a list that points to itself:
;;
;;    (let ((foo '(nil)))
;;      (setcar foo foo)
;;      foo)
;;
;;    => (#0)
;;
;;  In the above, the car of foo is set to foo.  Now if we pickel foo
;;  to a string, then unpickel that string, we produce an identical
;;  self-referential cons:
;;
;;    (let ((foo '(nil)))
;;      (setcar foo foo)
;;      (unpickel-string (pickel-to-string foo)))
;;
;;    => (#0)
;;
;;  Pickel also correctly deals with `eq' subobjects, including
;;  floats, strings, symbols and the collection types.  When two
;;  subobjects of an object are `eq', they will be `eq' after
;;  unpickeling as well:
;;
;;    (let* ((foo "bar")
;;           (baz (unpickel-string
;;                  (pickel-to-string (list foo foo)))))
;;      (eq (car baz) (cadr baz)))
;;
;;  => t
;;

;;; Installation:
;;
;;  - put `pickel.el' on your load path and (require 'pickel) where
;;    you want to use it.
;;

;;; Usage:
;;
;;  Pickeling:
;;
;;  To pickel an object to `standard-output':
;;
;;    (pickel obj)
;;
;;  To pickel an object to STREAM:
;;
;;    (pickel obj stream)
;;
;;  To pickel an object to a file:
;;
;;    (pickel-to-file "/path/to/file" obj)
;;
;;  And to pickel and object to a string:
;;
;;    (pickel-to-string obj)
;;
;;
;;  Unpickeling will only work on objects that have been pickeled.
;;
;;  To unpickel an object from `standard-input':
;;
;;    (unpickel)
;;
;;  To unpickel an object from STREAM:
;;
;;    (unpickel stream)
;;
;;  To unpickel a file:
;;
;;    (unpickel-file "/path/to/file")
;;
;;  And to unpickel a string:
;;
;;    (unpickel-string string)
;;

;;; TODO:
;;
;;  - Add types: char-tables
;;  - Add serialization of symbol plists?
;;  - Add serialization of string properties?
;;

;;; Code:

(require 'cl)


;;; defvars

(defvar pickel-identifier '--pickeled!--
  "Symbol that identifies a stream as a pickeled object.")

(defvar pickel-pickelable-types
  '(integer float symbol string cons vector hash-table)
  "Types that pickel can serialize.")


;;; utils

(defun pickel-take (lst n)
  "Return a list of the first N elts in LST.
Non-recursive so we don't overflow the stack."
  (let (acc)
    (while (and lst (> n 0))
      (decf n)
      (push (pop lst) acc))
    (nreverse acc)))

(defun pickel-group (lst n)
  "Group LST into contiguous N-length sublists.
Non-recursive so we don't overflow the stack."
  (let (acc)
    (while lst
      (push (pickel-take lst n) acc)
      (setq lst (nthcdr n lst)))
    (nreverse acc)))

(defmacro pickel-dohash (bindings &rest body)
  "Prettify maphash."
  (declare (indent defun))
  (destructuring-bind (key val table &optional ret)
      bindings
    `(progn
       (maphash (lambda (,key ,val) ,@body) ,table)
       ,ret)))

(defmacro pickel-wrap (prefix suffix &rest body)
  "Wrap BODY in PREFIX and SUFFIX when ON is non-nil."
  (declare (indent defun))
  `(progn (princ ,prefix) ,@body (princ ,suffix)))


;;; generate bindings

(defun pickel-mksym (idx)
  "Return IDX as a base 52 symbol-name [a-zA-Z].
`t' and `nil' are reserved constants and can't be used, so append
1 to them when they come up."
  (let ((q (/ idx 52)) (name ""))
    (flet ((setname
            (i) (let ((i (if (< i 26) (+ 65 i) (+ 71 i))))
                  (setq name (concat (char-to-string i) name)))))
      (setname (mod idx 52))
      (while (not (zerop q))
        (setname (mod q 52))
        (setq q (/ q 52)))
      (when (or (equal name "t")
                (equal name "nil"))
        (setq name (concat name "1")))
      (make-symbol name))))

(defun pickel-generate-bindings (obj)
  "Return a table mapping subobjects of OBJ to symbols.
Symbol bindings are generated with `pickel-mksym'."
  (let ((bindings (make-hash-table :test 'eq)) (idx -1))
    (flet ((inner
            (obj)
            (let ((type (type-of obj)))
              (unless (member type pickel-pickelable-types)
                (error "Pickel can't serialize objects of type %s" type))
              (unless (gethash obj bindings)
                (puthash obj (pickel-mksym (incf idx)) bindings)
                (typecase obj
                  (cons
                   (inner (car obj))
                   (inner (cdr obj)))
                  (vector
                   (dotimes (i (length obj))
                     (inner (aref obj i))))
                  (hash-table
                   (pickel-dohash (key val obj)
                     (inner key)
                     (inner val))))))))
      (inner obj)
      bindings)))


;;; construct objects

(defun pickel-construct-integer (int)
  "Print INT's constructor."
  (princ int))

(defun pickel-construct-float (flt)
  "Print FLT's constructor."
  (princ flt))

(defun pickel-construct-string (str)
  "Print STR's constructor."
  (prin1 str))

(defun pickel-construct-cons (cons)
  "Print CONS's constructor."
  (princ "(c)"))

(defun pickel-construct-vector (vec)
  "Print VEC's constructor."
  (princ (format "(v %s)" (length vec))))

(defun pickel-construct-symbol (sym)
  "Print SYM's constructor."
  (princ (cond ((eq sym nil) "nil")
               ((eq sym t) "t")
               ((intern-soft sym) (format "'%s" sym))
               (t (format "(m \"%s\")" sym)))))

(defun pickel-construct-hash-table (table)
  "Print TABLE's constructor."
  (princ (format "(h '%s %s %s %s %s)"
                 (hash-table-test             table)
                 (hash-table-size             table)
                 (hash-table-rehash-size      table)
                 (hash-table-rehash-threshold table)
                 (hash-table-weakness         table))))

(defun pickel-construct-objects (bindings)
  "Print the binds and constructors of objects in BINDINGS."
  (let ((first t))
    (pickel-wrap "(" ")"
      (pickel-dohash (obj bind bindings)
        (if first (setq first nil) (princ " "))
        (princ bind)
        (princ " ")
        (etypecase obj
          (integer    (pickel-construct-integer    obj))
          (float      (pickel-construct-float      obj))
          (string     (pickel-construct-string     obj))
          (cons       (pickel-construct-cons       obj))
          (vector     (pickel-construct-vector     obj))
          (symbol     (pickel-construct-symbol     obj))
          (hash-table (pickel-construct-hash-table obj)))))))


;;; link objects

(defun pickel-princer (obj)
  "princ OBJ's binding."
  (princ (gethash obj bindings)))

(defun pickel-link-cons (cons bind)
  "Set the car and cdr of BIND to the car and cdr of CONS."
  (pickel-wrap (format "(s %s " bind) ")"
    (pickel-princer (car cons))
    (princ " ")
    (pickel-princer (cdr cons))))

(defun pickel-link-vector (vec bind)
  "Set the vector cells of BIND to the vector cells of VEC."
  (dotimes (i (length vec))
    (pickel-wrap (format "(a %s %s " bind i) ")"
      (pickel-princer (aref vec i)))))

(defun pickel-link-hash-table (table bind)
  "Set the keys and vals of BIND to the keys and vals of TABLE."
  (pickel-dohash (key val table)
    (pickel-wrap (format "(p %s " bind) ")"
      (pickel-princer key)
      (princ " ")
      (pickel-princer val))))

(defun pickel-link-objects (bindings)
  "Call the link function for each object in BINDINGS."
  (pickel-wrap "(" ")"
    (pickel-dohash (obj bind bindings)
      (typecase obj
        (cons       (pickel-link-cons       obj bind))
        (vector     (pickel-link-vector     obj bind))
        (hash-table (pickel-link-hash-table obj bind))))))


;;; pickel

(defun pickel (obj &optional stream)
  "Serialize OBJ to STREAM or `standard-output'."
  (let ((standard-output (or stream standard-output))
        (bindings (pickel-generate-bindings obj)))
    (pickel-wrap (format "(%s " pickel-identifier) ")"
      (pickel-construct-objects bindings)
      (pickel-link-objects bindings)
      (pickel-princer obj))))

(defun pickel-to-string (obj)
  "`pickel' OBJ to a string, and return the string."
  (with-output-to-string (pickel obj)))

(defun pickel-to-file (file obj)
  "`pickel' OBJ to FILE."
  (with-temp-buffer
    (pickel obj (current-buffer))
    (write-file file)))


;;; unpickel

(defun unpickel (&optional stream)
  "Deserialize an object from STREAM or `standard-input'."
  (let ((expr (read (or stream standard-input)))
        (bindings (make-hash-table)))
    (unless (and (consp expr) (eq (car expr) pickel-identifier))
      (error "Attempt to unpickel a non-pickeled stream."))
    (condition-case err
        (flet ((m (str) (make-symbol str))
               (c () (cons nil nil))
               (v (len) (make-vector len nil))
               (h (ts sz rs rt w)
                  (make-hash-table :test ts :size sz :rehash-size rs
                                   :rehash-threshold rt :weakness w))
               (getbind (sym) (gethash sym bindings)))
          (dolist (binding (pickel-group (nth 1 expr) 2))
            (puthash (car binding) (eval (cadr binding)) bindings))
          (dolist (linker (nth 2 expr))
            (destructuring-bind (op a0 a1 a2) linker
              (case op
                (a (aset (getbind a0) a1 (getbind a2)))
                (p (puthash (getbind a1) (getbind a2) (getbind a0)))
                (s (let ((c (getbind a0)))
                     (setcar c (getbind a1))
                     (setcdr c (getbind a2)))))))
          (getbind (nth 3 expr)))
      (error (error "Error unpickeling %s: %s" stream err)))))

(defun unpickel-file (file)
  "`unpickel' an object directly from FILE."
  (with-temp-buffer
    (insert-file-contents file)
    (goto-char (point-min))
    (unpickel (current-buffer))))

(defun unpickel-string (str)
  "`unpickel' and object directly from STR."
  (with-temp-buffer
    (insert str)
    (goto-char (point-min))
    (unpickel (current-buffer))))


;;; provide

(provide 'pickel)


;;; end of pickel.el
