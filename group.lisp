;;;; Group evaluator

;;; A monoid is represented as an object containing a monoid presentation in the form of generators, which can be any 
;;;   s-expression, and relations, which are either expressions (if the expression is taken to evaluate to the identity)
;;;   or a list of two expressions (if the first expression is taken to evaluate to the second). 
;;; An expression is simply a list of generators. The identity is represented by the empty list (), and the group product
;;;   of two expressions is represented by their concatenation, given by the function GROUP-MULTIPLY. The inverse of an 
;;;   expression, if it exists, is calculated by the function GROUP-INVERT, which returns a list composed of inverses of
;;;   generators (represented as (- <generator>) if the generator is not itself an inverse). The function EXPRESSION-P
;;;   returns T for valid expressions in the given monoid.
;;; A group is a particular type of monoid where every generator is guaranteed to have an inverse. For every generator in
;;;   a particular presentation of a group, its respective inverse is also considered to be a generator, and for every
;;;   relation in the group presentation, its respective inverse is considered to be a relation, as well as relations
;;;   connecting each generator to its inverse.
;;; The method EVALUATE reduces a given expression as far as possible based on the presentation of the given monoid. In order
;;;   for that to work, the relations of a given group or monoid are completed using the Knuth-Bendix completion algorithm
;;;   which converts relations into a confluent term rewriting system. This algorithm is not guaranteed to terminate, as 
;;;   the problem of evaluating monoid/group expressions is in general undecidable.

(defpackage :GROUP-EVALUATOR
  (:use :COMMON-LISP)
  (:export :MONOID :GROUP
           :EVALUATE
           :ELEMENTS
           :EXPRESSION-P
           :GROUP-MULTIPLY
           :GROUP-INVERT))

(in-package :GROUP-EVALUATOR)

(defclass monoid ()
  ((generators :accessor generators :initarg :generators)
   (relations  :accessor relations  :initarg :relations)))
   
(defclass group (monoid) ())

(defmethod initialize-instance :after ((g group) &key generators relations)
  (let ((inverses (mapcar #'group-invert generators)))
    (nconc (generators g) inverses)
    (nconc (relations g) 
           (mapcar #'group-multiply generators inverses)
           (mapcar #'group-multiply inverses generators)
           (mapcar #'group-invert (relations g))) ;considers each relation to be a single expression
    (setf (relations g) (knuth-bendix g)))) ;TODO add this to the initializer of monoid as well
           
(defmethod evaluate ((m monoid) expr)
  ;; evaluate expr using each relation of group until not applicable
  (do ((rels (relations m)) new-expr)
      ((null rels) expr)
      (setf new-expr (reduce-expr expr (car rels)))
      (if (equal expr new-expr)
          (pop rels)
          (setf expr new-expr
                rels (relations m)))))
                       
(defun reduce-expr (expr rel &aux (lhs (first rel)) (rhs (second rel)) (len (length lhs)))
  "Replace each instance of (FIRST REL) in EXPR with (SECOND REL)."
  (do ((pos (search lhs expr :test #'equal) 
            (search lhs expr :test #'equal)))
      ((null pos) expr)
      (setf expr
        (append (subseq expr 0 pos)
                rhs
                (subseq expr (+ pos len))))))
  
(defmethod elements ((m monoid))
  "Return the different elements of M, assumed to be finite, by traversing its Cayley graph."
  (do* ((stack (list NIL) (cdr stack))
        (visited stack))
       ((null stack) (sort visited (lambda (a b) (shortlex< m a b))))
       (dolist (gen (generators m))
         (let ((new (evaluate m (cons gen (car stack)))))
           (unless (member new visited :test #'equal)
             (push new (cdr stack)))))))
  
;; quick hack, doesn't work for <x, y | x^3 = y^3 = (xy)^3 = 1>
(defmethod knuth-bendix ((m monoid))
  "Extend relations into confluent term rewriting system, if possible.
A rewriting rule is represented as a list of two terms, the LHS and the RHS."
  ;; go through each relation
  (do* ((rels (mapcar (lambda (e) (make-relation e m)) (relations m)) (cdr rels)) ;unvisited rels
        (res rels) rel)
       ((null rels) (remove-duplicates res :test #'equal)) ;quick hack, fix addition of new relations
       START
       (setf rel (car rels))
       ;; arrange rel so the rhs precedes the lhs 
       (when (shortlex< m (first rel) (second rel))
         (setf (values (first rel) (second rel))
               (values (second rel) (first rel))))
       ;; check if rel can be reduced
       (do ((res1 res (cdr res1)) new-lhs)
           ((null res1))
           ;; see if rel can be reduced by (car res1)
           (unless (equal (car res1) rel)
             (setf new-lhs (reduce-expr (first rel) (car res1)))
             (unless (equal new-lhs (first rel)) ;when it does reduce
               (setf (values (first rel) (second rel))
                     (values new-lhs
                             (reduce-expr (second rel) (car res1)))))))
       ;; if rel is trivial, i.e. its lhs and rhs are the same, remove and skip it
       (when (equal (first rel) (second rel))
         (setf rels (cdr rels))
         (loop with whole = (cons NIL res)
               for rest on whole
               until (null (cdr rest))
               for first = (cadr rest)
               if (eq first rel)
               do (setf (cdr rest) (cddr rest))
               finally (setf res (cdr whole)))
         (go START))
       ;; find overlaps with rel
       (do ((rels1 (cdr rels) (cdr rels1)) rel1 a b c r1 r2)
           ((null rels1))
           (setf rel1 (car rels1))
           (when (setf (values a b c) (find-overlaps (first rel) (first rel1)))
             (setf r1 (reduce-expr (append a b c) rel)
                   r2 (reduce-expr (append a b c) rel1))
             ;; add new relation connecting r1 and r2
             (unless (equal r1 r2)
               (let ((new-rel (sort (list r1 r2)
                                (lambda (a b)
                                  (shortlex< m b a)))))
                 (pushnew new-rel res :test #'equal) ;should be pushed to the back
                 (pushnew new-rel (cdr rels) :test #'equal)
                 ;; remove relations with reducible lhs from res, rels and rels1
                 (loop with whole = (cons NIL res)
                       for rest on whole
                       until (null (cdr rest))
                       for first = (cadr rest)
                       for new-lhs = (reduce-expr (first first) new-rel)
                       unless (equal first new-rel)
                       unless (equal (first first) new-lhs)
                       do (setf (cdr rest) (cddr rest))
                       finally (setf res (cdr whole)))))))))
                       
(defun find-overlaps (expr1 expr2 &aux (len1 (length expr1)) (len2 (length expr2)))
  "Return (values A B C) if the arguments are of the form AB and BC or ABC and B, else return NIL."
  (and expr1 expr2
    ;; set up common substring matrix for easier analysis
    (do ((e1 expr1 (cdr e1)) (i 0 (1+ i))
         (lens (make-array (list len1 len2)
                 :initial-element 0)))
        ((null e1)
         ;; traverse bottom row
         (do ((j 0 (1+ j)) val (ind 0))
             ((= j len2)
              ;; traverse rightmost column
              (if (> ind 0)
                  (values (subseq expr1 0 (- len1 ind)) ;A
                          (subseq expr2 0 ind) ;B
                          (subseq expr2 ind))  ;C
                  (do ((i 0 (1+ i)))
                      ((= i len1)
                       (when (> ind 0)
                         (values (subseq expr2 0 (- len2 ind))
                                 (subseq expr1 0 ind)
                                 (subseq expr1 ind))))
                      (setf val (aref lens i (1- len2)))
                      (cond 
                        ((= val (1+ i))
                         ;; found a BC-AB case, remember it in case there is a larger one
                         (setf ind val))
                        ((= val len2)
                         ;; found an ABC-B case
                         (return-from NIL 
                           (values (subseq expr1 0 (1+ (- i len2)))
                                   expr2
                                   (subseq expr1 (1+ i)))))))))
             (setf val (aref lens (1- len1) j))
             (cond 
               ((= val (1+ j))
                ;; found an AB-BC case, remember it in case there is a larger one
                (setf ind val))
               ((= val len1)
                ;; found a B-ABC case
                (return-from NIL 
                  (values (subseq expr2 0 (1+ (- j len1))) 
                          expr1 
                          (subseq expr2 (1+ j))))))))
        (do ((e2 expr2 (cdr e2)) (j 0 (1+ j)))
            ((null e2))
            (when (equal (car e1) (car e2)) ;incidence found
              (setf (aref lens i j)
                (if (and (> i 0) (> j 0))
                    (1+ (aref lens (1- i) (1- j))) ;look up if there is previous incidence
                    1))))))) ;start new incidence

(defmethod make-relation (rel (m monoid))
  "Convert a term into a relation if it isn't already one."
  (if (and (= (length rel) 2)
           (expression-p (first rel) m)
           (expression-p (second rel) m))
      rel
      (list rel NIL)))
  
(defmethod shortlex< ((g group) expr1 expr2)
  "Sort strings based on the order given on the generators of the group."
  ;; sort generators by their position in (generators g)
  (or (< (length expr1) (length expr2))
      (and expr2
        (= (length expr1) (length expr2))
        (loop for c1 in expr1
              for c2 in expr2
              for i1 = (position c1 (generators g) :test #'equal)
              for i2 = (position c2 (generators g) :test #'equal)
              if (or (not i1) (not i2)) return NIL
              if (< i1 i2) return T
              if (> i1 i2) return NIL))))
          
;;; Example

(defconstant klein 
  (make-instance 'group 
    :generators '(a b) 
    :relations '((a a) (b b) (a b a b))))

;;; Group implementation
  
(defmethod expression-p (expr (m monoid))
  "Return T if EXPR is a valid string in M."
  (and (listp expr)
       (subsetp expr (generators M) :test #'equal)))

(defun group-invert (expr)
  "Return the inverse of an expression."
  (cond ((null expr) NIL)
        ((atom expr) (list '- expr))
        ((eq (car expr) '-)
         (cadr expr))
        (T (reverse (mapcar #'group-invert expr)))))

(defun group-multiply (arg1 arg2)
  "Return the product of two expressions."
  (append (to-list arg1) (to-list arg2)))

(defun to-list (expr)
  (if (and (listp expr) (not (eq (car expr) '-))) expr (list expr)))
