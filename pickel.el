;;; pickel.el --- elisp object serialization

;; Copyright (C) 2010 tlh <thunkout@gmail.com>

;; File:      pickel.el
;; Author:    tlh <thunkout@gmail.com>
;; Created:   2010-09-29
;; Version:   0.71
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
;;  Pickel can serialize and deserialize most elisp objects, including
;;  any combination of lists (conses and nil), vectors, structs,
;;  hash-tables, strings, numbers and symbols.  It can't serialize
;;  functions, subroutines or opaque C types like
;;  window-configurations.
;;
;;  Pickel correctly detects cycles in the object graph.  So for
;;  instance, when a list points to itself:
;;
;;    (let* ((foo (list nil))
;;           (bar (list foo)))
;;      (setcar foo bar)
;;      bar)
;;
;;    => ((#0))
;;
;;  In the above, the car of foo is bar, and the car of bar is foo.
;;  Now, if we pickel bar to the current buffer, then evaluate the
;;  pickeled code, we get the same thing:
;;
;;    (let* ((foo (list nil))
;;           (bar (list foo)))
;;      (setcar foo bar)
;;      (pickel bar (current-buffer)))
;;
;;    ( ... pickled object here ... )
;;
;;    => ((#0))
;;
;;  When two components of an object are `eq', they will be equal
;;  after deserialization as well:
;;
;;    (let* ((foo "bar")
;;           (baz (list foo foo)))
;;      (pickel baz (current-buffer)))
;;
;;  (let ((quux ( ... pickeled object here ... )))
;;    (eq (car quux) (cadr quux)))
;;
;;  => t
;;
;;  To pickel an object:
;;
;;    (pickel obj stream)
;;
;;  And to unpickel an object:
;;
;;    (unpickel stream)
;;

;;; Installation:
;;
;;  - put `pickel.el' on your load path
;;
;;  - add this line to your `.emacs' file:
;;
;;    (require 'pickel)
;;


;;; Code:


(require 'cl)


;;; defvars

(defvar pickel-minimized-functions
  '("(m(s)(makunbound s))"
    "(c(a d)(cons a d))"
    "(sa(c a)(setcar c a))"
    "(sd(c d)(setcdr c d))"
    "(v(l i)(make-vector l i))"
    "(mht(&rest a)(apply 'make-hash-table a))"
    "(p(k v ht)(puthash k v ht))"
    "(a(v i e)(aset v i e))")
  "Smaller versions of object constructors to minimize pickled
  object size.")


;;; utils

(defun pickel-assoq (obj lst)
  "Like assoc, but tests with `eq'."
  (some (lambda (elt) (and (eq (car elt) obj) elt)) lst))

(defmacro pickel-dohash (bindings &rest body)
  "Prettify maphash."
  (declare (indent defun))
  (destructuring-bind (key val hash &optional return-form) bindings
    `(progn
       (maphash (lambda (,key ,val) ,@body) ,hash)
       ,return-form)))

(defun pickel-simple-type-p (obj)
  "Return t if OBJ doesn't need special `eq' treatment."
  (typecase obj
    (number t)
    (symbol t)
    (null   t)
    (t      nil)))


;;; generate bindings

(defun pickel-bindings (obj)
  "Return alist mapping unique subobjects of OBJ to symbols.
Only objects which need special `eq' treatment are added."
  (let (bindings)
    (flet ((inner
            (obj)
            (unless (or (pickel-simple-type-p obj)
                        (pickel-assoq obj bindings))
              (push (cons obj (gensym)) bindings)
              (typecase obj
                (cons
                 (inner (car obj))
                 (inner (cdr obj)))
                (vector
                 (dotimes (idx (length obj))
                   (inner (aref obj idx))))
                (hash-table
                 (pickel-dohash (key val obj)
                   (inner key)
                   (inner val)))))))
      (inner obj)
      bindings)))


;;; construction

(defun pickel-print-simple (obj)
  "Return t if OBJ doesn't require a constructor."
  (typecase obj
    (number     (prin1 obj))
    (string     (prin1 obj))
    (null       (prin1 obj))
    (symbol     (princ (format "'%s" obj)))))

(defun pickel-print-constructor (obj)
  "Print OBJ's type's constructor."
  (typecase obj
    (string     (prin1 obj))
    (cons       (princ "(c nil nil)"))
    (vector     (princ (format "(v %s nil)" (length obj))))
    (hash-table (princ (format "(mht :test '%S :size %S \
:rehash-size %S :rehash-threshold %S :weakness %S)"
                               (hash-table-test obj)
                               (hash-table-size obj)
                               (hash-table-rehash-size obj)
                               (hash-table-rehash-threshold obj)
                               (hash-table-weakness obj))))
    (t (error "Can't serialize type: %S" (type-of obj)))))

(defun pickel-print-obj (obj)
  "Print OBJ if it's simple.  Otherwise print OBJ's binding."
  (if (pickel-simple-type-p obj)
      (pickel-print-simple obj)
    (princ (cdr (pickel-assoq obj bindings)))))


;;; linking

(defun pickel-link-cons (cons sym)
  "Set the car and cdr of SYM to the car and cdr of CONS."
  (princ (format "(sa %s " sym))
  (pickel-print-obj (car cons))
  (princ (format ")(sd %s " sym))
  (pickel-print-obj (cdr cons))
  (princ ")"))

(defun pickel-link-vector (vec sym)
  "Set the vector cells of SYM to the vector cells of VEC."
  (dotimes (i (length vec))
    (princ (format "(a %s %s " sym i))
    (pickel-print-obj (aref vec i))
    (princ ")")))

(defun pickel-link-hash-table (table sym)
  "Set the keys and vals of SYM to the keys and vals of TABLE."
  (pickel-dohash (key val table)
    (princ "(p ")
    (pickel-print-obj key)
    (princ " ")
    (pickel-print-obj val)
    (princ (format " %s)" sym))))

(defun pickel-link-objects (obj sym)
  "Dispatch to OBJ and SYM's apropriate link function."
  (etypecase obj
    (string     nil)
    (cons       (pickel-link-cons       obj sym))
    (vector     (pickel-link-vector     obj sym))
    (hash-table (pickel-link-hash-table obj sym))))


;;; interface

(defun pickel (obj &optional stream)
  "Pickel OBJ to STREAM or `standard-output'."
  (let ((standard-output (or stream standard-output))
        (bindings (pickel-bindings obj)))
    (princ "(flet(")
    (mapc 'princ pickel-minimized-functions)
    (princ ")(let (")
    (dolist (binding bindings)
      (princ (format "(%s " (cdr binding)))
      (pickel-print-constructor (car binding))
      (princ ")"))
    (princ ")")
    (dolist (binding bindings)
      (pickel-link-objects (car binding) (cdr binding)))
    (pickel-print-obj obj)
    (princ "))")))

(defun unpickel (&optional stream)
  "Depickel and return an object from STREAM or
`standard-input'."
  (eval (read (or stream standard-input))))

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
