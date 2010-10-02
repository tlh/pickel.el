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
;;  lists (conses), vectors, hash-tables, strings, integers, floats,
;;  symbols and structs (vectors).  It can't serialize functions,
;;  subrs (subroutines) or opaque C types like window-configurations.
;;
;;  pickel works by printing out elisp that evaluates to an object
;;  "equal" to the object on which it's called.  So unpickeling an
;;  object amounts to evaluating the pickeled object.
;;
;;  pickel correctly reconstructs cycles in the object graph.  Take
;;  for instance a list that points to itself:
;;
;;    (let ((foo (list nil)))
;;      (setcar foo foo)
;;      foo) ;; <- evaluate this
;;
;;    => (#0)
;;
;;  In the above, the car of foo is set to foo.  Now if we pickel foo
;;  to the current buffer, then evaluate the code it produces, we get
;;  the same thing:
;;
;;    (let ((foo '(bar)))
;;      (setcar foo foo)
;;      (pickel foo (current-buffer)))
;;
;;    => ( ... pickled object here ... ) ;; <- evaluate this
;;
;;    => (#0)
;;
;;  Pickel also correctly deals with `eq' subobjects, including
;;  floats, strings, symbols and the collection types.  When two
;;  subobjects of an object are `eq', they will be `eq' after
;;  unpickeling as well:
;;
;;    (let ((foo "bar"))
;;      (pickel (list foo foo) (current-buffer)))
;;
;;  => ( ... pickled object ... )
;;
;;    (let ((quux ( ... pickeled object ... )))
;;      (eq (car quux) (cadr quux))) ;; <- evaluate this
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
;;  To pickel an object to `standard-output':
;;
;;    (pickel obj)
;;
;;  To pickel an object to STREAM:
;;
;;    (pickel obj stream)
;;
;;  To unpickel an object from `standard-input':
;;
;;    (unpickel)
;;
;;  And to unpickel an object from STREAM:
;;
;;    (unpickel stream)
;;
;;  Two functions are provided for pickeling and unpickeling to and
;;  from files:
;;
;;    (pickel-to-file obj "/path/to/file")
;;
;;    (unpickel-file "/path/to/file")
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

(defvar pickel-minimized-functions
  '((symbol
     . ("(m(s)(make-symbol s))"))
    (cons
     . ("(c(a d)(cons a d))"
        "(a(c a)(setcar c a))"
        "(d(c d)(setcdr c d))"))
    (vector
     . ("(v(l i)(make-vector l i))"
        "(s(v i e)(aset v i e))"))
    (hash-table
     . ("(h(ts sz rs rt w)(make-hash-table :test ts :size sz \
:rehash-size rs :rehash-threshold rt :weakness w))"
        "(p(k v ht)(puthash k v ht))")))
  "Smaller versions of object construction functions to minimize
  pickled object size.")


;;; utils

(defmacro pickel-dohash (bindings &rest body)
  "Prettify maphash."
  (declare (indent defun))
  (destructuring-bind (key val table &optional ret)
      bindings
    `(progn
       (maphash (lambda (,key ,val) ,@body) ,table)
       ,ret)))

(defmacro pickel-wrap? (prefix suffix on &rest body)
  "Wrap BODY in PREFIX and SUFFIX when ON is non-nil."
  (declare (indent defun))
  `(progn (and ,on (princ ,prefix))
          ,@body
          (and ,on (princ ,suffix))))

(defmacro pickel-wrap (prefix suffix &rest body)
  "Wrap BODY in PREFIX and SUFFIX."
  (declare (indent defun))
  `(pickel-wrap? ,prefix ,suffix t ,@body))


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

(defun pickel-traverse-obj (obj)
  "Return a list of data about OBJ, including: A hash table
containing the symbols of all the data types used in obj; a hash
table mapping unique subobjects of OBJ to symbols generated with
`pickel-mksym' -- only objects which need special `eq' treatment
are added; and a flag representing whether or not any bindings
were generated."
  (let ((bindings (make-hash-table :test 'eq))
        (type-flags (make-hash-table)) (idx -1))
    (flet ((inner
            (obj)
            (let ((type (type-of obj)))
              (unless (member type pickel-pickelable-types)
                (error "Pickel can't serialize objects of type %s" type))
              (unless (or (pickel-no-bind-p obj) (gethash obj bindings))
                (puthash type t type-flags)
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
      (list type-flags bindings (< -1 idx)))))


;;; object construction

(defun pickel-print-float-constructor (flt)
  "Print the constructor for FLT."
  (princ flt))

(defun pickel-print-symbol-constructor (sym)
  "Print the constructor for SYM.
If obj is interned at pickel-time, re-intern it at
depickel-time (i). If not, make an uninterned symbol (s)."
  (princ (if (intern-soft sym)
             (format "'%s" sym)
           (format "(m %S)" (symbol-name sym)))))

(defun pickel-print-string-constructor (str)
  "Print the constructor for STR."
  (prin1 str))

(defun pickel-print-cons-constructor (cns)
  "Print the constructor for CNS."
  (princ "(c 0 0)"))

(defun pickel-print-vector-constructor (vec)
  "Print the constructor for VEC."
  (princ (format "(v %s 0)" (length vec))))

(defun pickel-print-hash-table-constructor (table)
  "Print the constructor for TABLE.
All hash-table properties are set."
  (princ (format "(h '%s %s %s %s %s)"
                 (hash-table-test             table)
                 (hash-table-size             table)
                 (hash-table-rehash-size      table)
                 (hash-table-rehash-threshold table)
                 (hash-table-weakness         table))))

(defun pickel-print-constructor (obj)
  "Print OBJ's constructor."
  (etypecase obj
    (float      (pickel-print-float-constructor      obj))
    (symbol     (pickel-print-symbol-constructor     obj))
    (string     (pickel-print-string-constructor     obj))
    (cons       (pickel-print-cons-constructor       obj))
    (vector     (pickel-print-vector-constructor     obj))
    (hash-table (pickel-print-hash-table-constructor obj))))

(defun pickel-print-obj (obj)
  "Print OBJ if it's an integer, its binding otherwise."
  (princ (or (gethash obj bindings) obj)))


;;; object linking

(defun pickel-link-cons (cons bind)
  "Set the car and cdr of BIND to the car and cdr of CONS."
  (pickel-wrap (format "(a %s " bind) ")"
    (pickel-print-obj (car cons)))
  (pickel-wrap (format "(d %s " bind) ")"
    (pickel-print-obj (cdr cons))))

(defun pickel-link-vector (vec bind)
  "Set the vector cells of BIND to the vector cells of VEC."
  (dotimes (i (length vec))
    (pickel-wrap (format "(s %s %s " bind i) ")"
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


;;; pickel interface

(defun pickel (obj &optional stream)
  "Pickel OBJ to STREAM or `standard-output'."
  (let ((standard-output (or stream standard-output)))
    (destructuring-bind (type-flags bindings binds?)
        (pickel-traverse-obj obj)
      (pickel-wrap (format "(progn '%s " pickel-identifier) ")"
        (pickel-wrap? "(flet" ")" binds?
          (pickel-wrap? "(" ")" binds?
            (dolist (elt pickel-minimized-functions)
              (when (gethash (car elt) type-flags)
                (mapc 'princ (cdr elt)))))
          (pickel-wrap? "(let" ")" binds?
            (pickel-wrap? "(" ")" binds?
              (when binds?
                (pickel-dohash (obj bind bindings)
                  (pickel-wrap (format "(%s " bind) ")"
                    (pickel-print-constructor obj)))))
            (pickel-link-objects bindings)
            (pickel-print-obj obj)))))))

(defun unpickel (&optional stream)
  "Unpickel an object from STREAM or `standard-input'.
Errors are thrown if the stream isn't a pickeled object, or if
there's an error evaluating the expression."
  (let* ((stream (or stream standard-input))
         (expr (read stream)))
    (unless (and (consp expr) (equal `(quote ,pickel-identifier) (cadr expr)))
      (error "Attempt to unpickel a non-pickeled stream."))
    (condition-case err
        (eval expr)
      (error (error "Error unpickeling %s: %s" stream err)))))

(defun pickel-to-file (obj file)
  "Pickel OBJ directly to FILE."
  (with-temp-buffer
    (pickel obj (current-buffer))
    (write-file file)))

(defun unpickel-file (file)
  "Depickel an object directly from FILE."
  (with-temp-buffer
    (insert-file-contents file)
    (goto-char (point-min))
    (unpickel (current-buffer))))


;;; provide

(provide 'pickel)


;;; end of pickel.el
