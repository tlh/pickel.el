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
;;  `pickel' works by printing to a stream a set of coded
;;  instructions, which can be used by `unpickel' to recreate the
;;  original object.  The unpickeled object isn't `eq' to the
;;  original, although the two are "equal" in the spirit of `equal',
;;  in the sense that their structure and content are equal.  For
;;  example:
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
;;  Pickel also correctly recreates `eq' subobjects, including
;;  strings, symbols, floats and the collection types.  When two
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

(defvar pickel-identifier '~pickel!~
  "Symbol identifying a stream as a pickel.")

(defvar pickel-types
  '(integer float symbol string cons vector hash-table)
  "Types pickel can serialize.")


;;; utils

(defun pickel-take (lst n)
  "Return a list of the first N elts in LST.
Iterative to avoid stack overflow."
  (let (acc)
    (while (and lst (> n 0))
      (decf n)
      (push (pop lst) acc))
    (nreverse acc)))

(defun pickel-group (lst n)
  "Group LST into contiguous N-length sublists.
Iterative to avoid stack overflow."
  (let (acc)
    (while lst
      (push (pickel-take lst n) acc)
      (setq lst (nthcdr n lst)))
    (nreverse acc)))

(defmacro pickel-dohash (bindings &rest body)
  "do-style wrapper for maphash."
  (declare (indent defun))
  (destructuring-bind (key val table &optional ret)
      bindings
    `(progn
       (maphash (lambda (,key ,val) ,@body) ,table)
       ,ret)))

(defmacro pickel-wrap (prefix suffix &rest body)
  "Wrap BODY in PREFIX and SUFFIX princers."
  (declare (indent defun))
  `(progn (princ ,prefix) ,@body (princ ,suffix)))


;;; generate bindings

(lexical-let ((idchs "0123456789abcdefghijklmnopqrstuvwxyzABCDEF\
GHIJKLMNOPQRSTUVWXYZ~!@$%^&*|<>-_=+/:"))
  (defun pickel-gid (i)
    "Return an id from I in base (length idchs)."
    (let ((base (length idchs)) id)
      (flet ((addch () (push (aref idchs (mod i base)) id)
                    (setq i (/ i base))))
        (addch) (while (> i 0) (addch))
        (map 'string 'identity id)))))

(defun pickel-generate-bindings (obj)
  "Return a hash-table mapping subobjects of OBJ to GIDs."
  (let ((binds (make-hash-table :test 'eq)) (i -1))
    (flet ((bind
            (obj)
            (let ((type (type-of obj)))
              (unless (memq type pickel-types)
                (error "Can't pickel type: %s" type))
              (unless (gethash obj binds)
                (puthash obj (pickel-gid (incf i)) binds)
                (case type
                  (cons
                   (bind (car obj)) (bind (cdr obj)))
                  (vector
                   (dotimes (j (length obj))
                     (bind j) (bind (aref obj j))))
                  (hash-table
                   (pickel-dohash (k v obj)
                     (bind k) (bind v)))))
              binds)))
      (bind obj))))


;;; create objects

(defun pickel-create-objects ()
  "Print the IDs and creators of all objects in BINDINGS."
  (pickel-wrap "(" ")"
    (pickel-dohash (obj id bindings)
      (princ
       (format
        "%s %s " id
        (etypecase obj
          (integer    obj)
          (float      obj)
          (string     (format "%S" obj))
          (cons       "(c)")
          (vector     (format "(v %s)" (length obj)))
          (symbol     (cond ((eq obj nil) "nil")
                            ((eq obj t)   "t")
                            ((intern-soft obj) (format "'%s" obj))
                            (t (format "(m %S)" (symbol-name obj)))))
          (hash-table (format "(h '%s %s %s %s %s)"
                              (hash-table-test             obj)
                              (hash-table-size             obj)
                              (hash-table-rehash-size      obj)
                              (hash-table-rehash-threshold obj)
                              (hash-table-weakness         obj)))))))))


;;; set objects

(defun pickel-set-objects ()
  "Print set instructions for collection objects in BINDINGS."
  (flet ((id (obj) (gethash obj bindings))
         (set (op a b c)
              (princ (format "%s %s %s %s "
                             op (id a) (id b) (id c)))))
    (pickel-wrap "(" ")"
      (pickel-dohash (obj id bindings)
        (typecase obj
          (cons
           (set 's obj (car obj) (cdr obj)))
          (vector
           (dotimes (i (length obj)) (set 'a obj i (aref obj i))))
          (hash-table
           (pickel-dohash (k v obj) (set 'p k v obj))))))))


;;; pickel

(defun pickel (obj &optional stream)
  "Serialize OBJ to STREAM or `standard-output'."
  (let ((standard-output (or stream standard-output))
        (bindings (pickel-generate-bindings obj)))
    (pickel-wrap "(" ")"
      (princ pickel-identifier)
      (pickel-create-objects)
      (pickel-set-objects)
      (princ (gethash obj bindings)))))

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
  (let ((pickel (read (or stream standard-input)))
        (bindings (make-hash-table)))
    (unless (and (consp pickel) (eq (car pickel) pickel-identifier))
      (error "Attempt to unpickel a non-pickeled stream."))
    (condition-case err
        (flet ((m (str) (make-symbol str))
               (c () (cons nil nil))
               (v (len) (make-vector len nil))
               (h (ts sz rs rt w)
                  (make-hash-table :test ts :size sz :rehash-size rs
                                   :rehash-threshold rt :weakness w))
               (setcons (cons a d) (setcar cons a) (setcdr cons d))
               (getbind (id) (gethash id bindings)))
          (dolist (elt (pickel-group (nth 1 pickel) 2))
            (puthash (car elt) (eval (cadr elt)) bindings))
          (dolist (elt (pickel-group (nth 2 pickel) 4))
            (apply (case (car elt) (a 'aset) (p 'puthash) (s 'setcons))
                   (mapcar 'getbind (cdr elt))))
          (getbind (nth 3 pickel)))
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
