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

(defun pickel-no-bind-p (obj)
  "Return t for objects that shouldn't get a binding."
  (or (eq obj t)
      (eq obj nil)
      (integerp obj)))

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
  "Return a list of data about OBJ, including: A hash table
containing the symbols of all the data types used in OBJ; a hash
table mapping unique subobjects of OBJ to symbols generated with
`pickel-mksym' -- only objects which need special `eq' treatment
are added; and a flag representing whether or not any bindings
were generated."
  (let ((bindings (make-hash-table :test 'eq)) (idx -1))
    (flet ((inner
            (obj)
            (let ((type (type-of obj)))
              (unless (member type pickel-pickelable-types)
                (error "Pickel can't serialize objects of type %s" type))
              (unless (or (pickel-no-bind-p obj) (gethash obj bindings))
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

(defun pickel-construct-float (flt)
  "Print FLT's constructor."
  (princ flt))

(defun pickel-construct-string (str)
  "Print STR's constructor."
  (prin1 str))

(defun pickel-construct-cons (cons)
  "Print CONS's constructor."
  (princ "(c 0 0)"))

(defun pickel-construct-vector (vec)
  "Print VEC's constructor."
  (princ (format "(v %s 0)" (length vec))))

(defun pickel-construct-symbol (sym)
  "Print SYM's constructor."
  (princ (if (intern-soft sym)
             (format "'%s" sym)
           (format "(m %S)" (symbol-name sym)))))

(defun pickel-construct-hash-table (table)
  "Print TABLE's constructor."
  (princ (format "(h '%s %s %s %s %s)"
                 (hash-table-test             table)
                 (hash-table-size             table)
                 (hash-table-rehash-size      table)
                 (hash-table-rehash-threshold table)
                 (hash-table-weakness         table))))

(defun pickel-construct-objects (bindings)
  "Print the constructors of all objects in BINDINGS."
  (pickel-wrap "(" ")"
    (pickel-dohash (obj bind bindings)
      (pickel-wrap (format "(%s " bind) ")"
        (etypecase obj
          (float      (pickel-construc-float       obj))
          (string     (pickel-construct-string     obj))
          (cons       (pickel-construct-cons       obj))
          (vector     (pickel-construct-vector     obj))
          (symbol     (pickel-construct-symbol     obj))
          (hash-table (pickel-construct-hash-table obj)))))))


;;; link objects

(defun pickel-print-obj (obj)
  "Print OBJ if it's an integer, its binding otherwise."
  (princ (or (gethash obj bindings) obj)))

(defun pickel-link-cons (cons bind)
  "Set the car and cdr of BIND to the car and cdr of CONS."
  (pickel-wrap (format "(s %s " bind) ")"
    (pickel-print-obj (car cons))
    (princ " ")
    (pickel-print-obj (cdr cons))))

(defun pickel-link-vector (vec bind)
  "Set the vector cells of BIND to the vector cells of VEC."
  (dotimes (i (length vec))
    (pickel-wrap (format "(a %s %s " bind i) ")"
      (pickel-print-obj (aref vec i)))))

(defun pickel-link-hash-table (table bind)
  "Set the keys and vals of BIND to the keys and vals of TABLE."
  (pickel-dohash (key val table)
    (pickel-wrap "(p " (format " %s)" bind)
      (pickel-print-obj key)
      (princ " ")
      (pickel-print-obj val))))

(defun pickel-link-objects (bindings)
  "Dispatch to OBJ's apropriate link function."
  (pickel-dohash (obj bind bindings)
    (typecase obj
      (cons       (pickel-link-cons       obj bind))
      (vector     (pickel-link-vector     obj bind))
      (hash-table (pickel-link-hash-table obj bind)))))


;;; pickel

(defun pickel (obj &optional stream)
  "Pickel OBJ to STREAM or `standard-output'."
  (let ((standard-output (or stream standard-output))
        (bindings (pickel-generate-bindings obj)))
    (pickel-wrap (format "(%s " pickel-identifier) ")"
      (pickel-construct-objects bindings)
      (pickel-link-objects bindings)
      (pickel-print-obj obj))))

(defun pickel-to-string (obj)
  (with-output-to-string (pickel obj)))

(defun pickel-to-file (file obj)
  "Pickel OBJ directly to FILE."
  (with-temp-buffer
    (pickel obj (current-buffer))
    (write-file file)))


;;; unpickel

(defun unpickel (&optional stream)
  "Unpickel an object from STREAM or `standard-input'.
Errors are thrown if the stream isn't a pickeled object, or if
there's an error evaluating the expression."
  (let ((expr (read (or stream standard-input))))
    (unless (and (consp expr) (eq pickel-identifier (car expr)))
      (error "Attempt to unpickel a non-pickeled stream."))
    (flet ((m (str) (make-symbol str))
           (c (obj1 obj2) (cons obj1 obj2))
           (s (cons obj1 obj2) (setcar cons obj1) (setcdr cons obj2))
           (v (len init) (make-vector len init))
           (a (vec idx obj) (aset vec idx obj))
           (p (key val table) (puthash key val table))
           (h (ts sz rs rt w)
              (make-hash-table :test ts :size sz :rehash-size rs
                               :rehash-threshold rt :weakness w)))
      (condition-case err
          (eval `(let ,(cadr expr) ,@(cddr expr)))
        (error (error "Error unpickeling %s: %s" stream err))))))

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
