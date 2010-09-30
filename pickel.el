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
;;  Pickel can serialize and deserialize most elisp objects, including
;;  any combination of lists (conses and nil), vectors, structs,
;;  hash-tables, strings, numbers and symbols.  It can't serialize
;;  functions, subroutines or opaque C types like
;;  window-configurations.
;;
;;  Pickel correctly detects cycles in the object graph.  Take for
;;  instance a list that points to itself:
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
;;    (let ((foo (list nil)))
;;      (setcar foo foo)
;;      (pickel foo (current-buffer))) ;; <- evaluate this
;;
;;    => ( ... pickled object here ... ) ;; <- evaluate this
;;
;;    => (#0)
;;
;;  When two components of an object are `eq', they will be equal
;;  after unpickeling as well:
;;
;;    (let* ((foo "bar")
;;           (baz (list foo foo)))
;;      (pickel baz (current-buffer)))
;;
;;  => ( ... pickled object here ... )
;;
;; (let ((quux ( ... pickeled object here ... )))
;;    (eq (car quux) (cadr quux))) ;; <- evaluate this
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
;;  To pickel an object to STREAM
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
;;  Two functions are included for working directly with files:
;;
;;    (pickel-to-file obj "/path/to/file")
;;
;;    (unpickel-file "/path/to/file")
;;

;;; TODO:
;;
;;  - Add serialization of propertized strings
;;

;;; Code:


(require 'cl)


;;; defvars

(defvar pickel-identifier '--pickel--
  "Symbol that identifies a stream as a pickeled object.")

(defvar pickel-minimized-functions
  '((cons-fns
     . ("(c(a d)(cons a d))"
        "(sa(c a)(setcar c a))"
        "(sd(c d)(setcdr c d))"))
    (vector-fns
     . ("(v(l i)(make-vector l i))"
        "(a(v i e)(aset v i e))"))
    (hash-table-fns
     . ("(mht(ts sz rs rt w)(make-hash-table :test ts :size sz \
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

(defun pickel-simple-type-p (obj)
  "Return t if OBJ doesn't need special `eq' treatment."
  (typecase obj (number t) (symbol t) (t nil)))


;;; generate bindings

(defun pickel-generate-bindings (obj)
  "Return alist mapping unique subobjects of OBJ to symbols.
Only objects which need special `eq' treatment are added.  Since
this function sees every subobject of OBJ, it is also used to
flag which sets of constructor functions to include in the
pickeled object."
  (let ((bindings (make-hash-table)) (i -1))
    (flet ((inner
            (obj)
            (unless (or (pickel-simple-type-p obj)
                        (gethash obj bindings))
              (puthash obj (intern (format "p%s" (incf i))) bindings)
              (etypecase obj
                (string)
                (cons
                 (setq cons-flag t)
                 (inner (car obj))
                 (inner (cdr obj)))
                (vector
                 (setq vector-flag t)
                 (dotimes (idx (length obj))
                   (inner (aref obj idx))))
                (hash-table
                 (setq hash-table-flag t)
                 (pickel-dohash (key val obj)
                   (inner key)
                   (inner val)))))))
      (inner obj)
      bindings)))


;;; object construction

(defun pickel-print-fns (type)
  "`princ' TYPE's constructor functions from
pickel-minimized-functions."
  (mapc 'princ (cdr (assoc type pickel-minimized-functions))))

(defun pickel-print-simple (obj)
  "`princ' the simple types."
  (etypecase obj
    (number (princ obj))
    (null   (princ obj))
    (symbol (princ (format "'%s" obj)))))

(defun pickel-print-constructor (obj)
  "Print OBJ's type's constructor."
  (etypecase obj
    (string     (prin1 obj))
    (cons       (princ "(c nil nil)"))
    (vector     (princ (format "(v %s nil)" (length obj))))
    (hash-table (princ (format "(mht '%s %s %s %s %s)"
                               (hash-table-test obj)
                               (hash-table-size obj)
                               (hash-table-rehash-size obj)
                               (hash-table-rehash-threshold obj)
                               (hash-table-weakness obj))))))

(defun pickel-print-obj (obj)
  "Print OBJ if it's simple.  Otherwise print OBJ's binding."
  (if (pickel-simple-type-p obj)
      (pickel-print-simple obj)
    (princ (gethash obj bindings))))


;;; object linking

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


;;; pickel interface

(defun pickel (obj &optional stream)
  "Pickel OBJ to STREAM or `standard-output'."
  (let* ((standard-output (or stream standard-output))
         cons-flag vector-flag hash-table-flag
         (bindings (pickel-generate-bindings obj)))
    (princ (format "(progn '%s(flet(" pickel-identifier))
    (when cons-flag
      (pickel-print-fns 'cons-fns))
    (when vector-flag
      (pickel-print-fns 'vector-fns))
    (when hash-table-flag
      (pickel-print-fns 'hash-table-fns))
    (princ ")(let(")
    (pickel-dohash (obj sym bindings)
      (princ (format "(%s " sym))
      (pickel-print-constructor obj)
      (princ ")"))
    (princ ")")
    (pickel-dohash (obj sym bindings)
      (pickel-link-objects obj sym))
    (pickel-print-obj obj)
    (princ ")))")))

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
