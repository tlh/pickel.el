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
;;  Pickel correctly detects cycles in the object graph, so when two
;;  components of an object are `eq', they will be equal after
;;  deserialization as well:
;;
;;    (let* ((foo "bar")
;;           (baz (list foo foo)))
;;      (pickel baz (current-buffer)))
;;
;;  (setq quux ( ... pickeled object here ... ))
;;  (eq (car quux) (cadr quux)) => t
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


;;; predicates

(defun pickel-simple-type-p (obj)
  "Return t if OBJ doesn't need special `eq' treatment."
  (typecase obj
    (number t)
    (symbol t)
    (null   t)
    (t      nil)))

(defun pickel-pickeled-p (obj)
  "Return t if OBJ has been pickeled, nil otherwise."
  (or (pickel-simple-type-p obj)
      (pickel-assoq obj pickeled)))

(defun pickel-components-pickeled-p (obj)
  "Return t if toplevel elts of OBJ have been pickeled."
  (typecase obj
    (string t)
    (cons
     (and (pickel-pickeled-p (car obj))
          (pickel-pickeled-p (cdr obj))))
    (vector
     (catch 'result
       (dotimes (idx (length obj) t)
         (unless (pickel-pickeled-p (aref obj idx))
           (throw 'result nil)))))
    (hash-table
     (catch 'result
       (pickel-dohash (key val obj t)
         (unless (and (pickel-pickeled-p key)
                      (pickel-pickeled-p val))
           (throw 'result nil)))))))


;;; printing

(defun pickel-print-pickeled (obj)
  "If OBJ's type is simple, print it.
If OBJ's type is composite, print the symbol it's bound to."
  (if (pickel-simple-type-p obj)
      (pickel-dispatch obj)
    (princ (cdr (pickel-pickeled-p obj)))))

(defun pickel-default (obj)
  "Serialize OBJ with `prin1'."
  (prin1 obj))

(defun pickel-symbol (sym)
  "Serialize symbol SYM."
  (princ "'")
  (princ sym))

(defun pickel-cons (cons)
  "Serialize CONS."
  (princ "(c ")
  (pickel-print-pickeled (car cons))
  (princ " ")
  (pickel-print-pickeled (cdr cons))
  (princ ")"))

(defun pickel-vector (vec)
  "Serialize VEC."
  (let ((len (length vec)))
    (princ (format "(let((_ (v %s nil)))" len))
    (dotimes (idx len)
      (princ (format "(a _ %s " idx))
      (pickel-print-pickeled (aref vec idx))
      (princ ")"))
    (princ "_)")))

(defun pickel-hash-table (table)
  "Serialize TABLE."
  (princ (format "(let((_(mht \
:test '%S :size %S :rehash-size %S \
:rehash-threshold %S :weakness %S)))"
                 (hash-table-test table)
                 (hash-table-size table)
                 (hash-table-rehash-size table)
                 (hash-table-rehash-threshold table)
                 (hash-table-weakness table)))
  (pickel-dohash (key val table)
    (princ "(p ")
    (pickel-print-pickeled key)
    (princ " ")
    (pickel-print-pickeled val)
    (princ " _)"))
  (princ "_)"))

(defun pickel-dispatch (obj)
  "Serialize OBJ, dispatching on its type."
  (typecase obj
    (number     (pickel-default    obj))
    (string     (pickel-default    obj))
    (null       (pickel-default    obj))
    (symbol     (pickel-symbol     obj))
    (cons       (pickel-cons       obj))
    (vector     (pickel-vector     obj))
    (hash-table (pickel-hash-table obj))
    (t (error "Can't serialize type: %S" (type-of obj)))))


;;; object graph cycle detection

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


;;; interface

(defun pickel (obj &optional stream)
  "Pickel OBJ to STREAM or `standard-output'."
  (let* ((standard-output (or stream standard-output))
         (unpickeled (pickel-bindings obj))
         (pickeled))
    (princ "(flet(")
    (mapc 'princ pickel-minimized-functions)
    (princ ")")
    (while unpickeled
      (dolist (binding unpickeled)
        (destructuring-bind (obj . sym) binding
          (when (pickel-components-pickeled-p obj)
            (princ (format "(setq %s " (cdr binding)))
            (pickel-dispatch (car binding))
            (princ ")")
            (push binding pickeled)
            (setq unpickeled (remove binding unpickeled))))))
    (princ "(prog1 ")
    (pickel-print-pickeled obj)
    (dolist (binding pickeled)
      (princ (format "(m '%s)" (cdr binding))))
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
