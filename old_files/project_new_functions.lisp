; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
;;new definitions for merge-ordered, with insert ordered
(defdata lor (listof rational))

(definec orderedp (l :lor) :bool
  (cond
   ((endp (cdr l)) t)
   (t (and (<= (car l) (cadr l)) (orderedp (rest l))))))

;;insert an element into an ordered list in the right place
(definec insert-ordered (elem :rational l :lor) :lor
  :ic (orderedp l)
  :oc (orderedp (insert-ordered elem l))
  (cond
   ((endp l) (list elem))
   ((<= elem (car l)) (cons elem l))
   (t (cons (car l) (insert-ordered elem (cdr l))))))
(set-gag-mode nil)
;mergeing ordered with repeated calls to insert-ordered
;if add (orderedp l1) to the :ic, ACL2 can't prove the function contracts
(definec merge-ordered-insert (l1 :lor l2 :lor) :lor
  :ic (orderedp l2)
  :oc (orderedp (merge-ordered-insert l1 l2))
  (if (endp l1)
    l2
    (insert-ordered (car l1) (merge-ordered-insert (cdr l1) l2))))

;4 parter
;pt 1
(thm (implies (and (rationalp a) (lorp b) (orderedp b) (lorp c) (orderedp c)
              (<= a (car b)) (<= a (car (merge-ordered-insert b c))))
(equal (merge-ordered-insert (cons a b) c) (cons a (merge-ordered-insert b c)))))#|ACL2s-ToDo-Line|#

;;trying to prove this?
;;stuff with two lists and merge-ordered-insert
(thm (implies
 (and (lorp (cons x y)) (orderedp (cons x y))
      (lorp (cons w v)) (orderedp (cons w v)))
 (or (and (<= x w)
          (equal (merge-ordered-insert (cons x y) (cons w v))
                 (cons x (merge-ordered-insert y (cons w v)))))
     (and (> x w)
          (equal (merge-ordered-insert (cons x y) (cons w v))
                 (cons w (merge-ordered-insert (cons x y) v))))))
     )
;pt2
#|
(thm (implies (and (rationalp a) (lorp b) (orderedp b) (lorp c) (orderedp c)
                   (ne-tlp a) (ne-tlp b)
              (<= a (car b)) (not (<= a (car (merge-ordered-insert b c)))))
(equal (merge-ordered-insert (cons a b) c)
(cons (car (merge-ordered-insert b c)) (insert-ordered a (cdr (merge-ordered-insert b c)))))))
|#


;pt 3
#|
(thm (implies (and (rationalp a) (lorp b) (orderedp b) (lorp c) (orderedp c) (ne-tlp b) (ne-tlp c)
              (not (<= a (car b))) (<= a (car (merge-ordered-insert b c))))
(equal (merge-ordered-insert (cons (car b) (insert-ordered a (cdr b))) c)
(cons a (merge-ordered-insert b c)))))
|#

;pt 4
#|
(thm (implies (and (rationalp a) (lorp b) (orderedp b) (lorp c) (orderedp c)
                   (ne-tlp b) (ne-tlp c)
              (not (<= a (car b))) (not (<= a (car (merge-ordered-insert b c)))))
(equal (merge-ordered-insert (cons (car b) (insert-ordered a (cdr b))) c)
(cons (car (merge-ordered-insert b c)) (insert-ordered a (cdr (merge-ordered-insert b c)))))))
|#

;;END CASES

;testing thms
(defthm car-cdr-insert-orderd (implies (and (lorp a) (consp a) (orderedp a))
                                      (equal (insert-ordered (car a) (cdr a))
                                             a)))
(skip-proofs (defthm insert-with-merge-2 (implies (and (rationalp a) (lorp b) (orderedp b) (lorp c) (orderedp c))
                                     (equal (merge-ordered-insert (insert-ordered a b) c)
                                            (insert-ordered a (merge-ordered-insert b c))))
  ))
(defthm new-thm (implies (and (lorp a) (orderedp a) (lorp b) (orderedp b) (lorp c) (orderedp c))
                         (equal (merge-ordered-insert (merge-ordered-insert a b) c)
                                (merge-ordered-insert a (merge-ordered-insert b c)))))

(defthm len-1-assoc (implies (and (rationalp a) (rationalp b) (rationalp c))
                             (equal (merge-ordered-insert (merge-ordered-insert (list a) (list b)) (list c))
                                    (merge-ordered-insert (list a) (merge-ordered-insert (list b) (list c))))))

(defthm len-1-assoc-2 (implies (and (rationalp a) (rationalp b) (lorp c) (orderedp c))
                               (equal (merge-ordered-insert (merge-ordered-insert (list a) (list b)) c)
                                      (merge-ordered-insert (list a) (merge-ordered-insert (list b) c)))))
;hard fails
#|
(defthm len-1-assoc-3 (implies (and (rationalp a) (lorp b) (orderedp b) (lorp c) (orderedp c))
                               (equal (merge-ordered-insert (merge-ordered-insert (list a) b) c)
                                      (merge-ordered-insert (list a) (merge-ordered-insert b c)))))
|#

(set-gag-mode t)
;spins forever
#|
(defthm len-1-assoc-4 (implies (and (lorp a) (orderedp a) (lorp b) (orderedp b) (rationalp c))
                               (equal (merge-ordered-insert (merge-ordered-insert a b) (list c))
                                      (merge-ordered-insert a (merge-ordered-insert b (list c))))))|#
;spins forever
#|
(defthm len-1-assoc-5 (implies (and (lorp a) (orderedp a) (rationalp b) (lorp c) (orderedp c))
                               (equal (merge-ordered-insert (merge-ordered-insert a (list b)) c)
                                      (merge-ordered-insert a (merge-ordered-insert (list b) c)))))
|#

#|
;;hints to possibly use, for reference
:hints (("Goal" :induct (lorp a)))
|#

;our actual theorem
#|
(defthm new-thm (implies (and (lorp a) (orderedp a) (lorp b) (orderedp b) (lorp c) (orderedp c))
                         (equal (merge-ordered-insert (merge-ordered-insert a b) c)
                                (merge-ordered-insert a (merge-ordered-insert b c)))))
|#


;the above thm fails with these three key-checkpoints goals under induction
;a is a single element
#|
(IMPLIES (AND (RATIONALP (CAR A))
              (CONSP A)
              (NOT (CDR A))
              (RATIONAL-LISTP B)
              (ORDEREDP B)
              (RATIONAL-LISTP C)
              (ORDEREDP C))
         (EQUAL (MERGE-ORDERED-INSERT (INSERT-ORDERED (CAR A) B)
                                      C)
                (INSERT-ORDERED (CAR A)
                                (MERGE-ORDERED-INSERT B C))))
|#
;a is a single element less than 0
;if you can prove the previous one, why is this one here?
#|
(IMPLIES (AND (RATIONALP (CAR A))
              (NOT (CDR A))
              (CONSP A)
              (<= (CAR A) 0)
              (RATIONAL-LISTP B)
              (ORDEREDP B)
              (RATIONAL-LISTP C)
              (ORDEREDP C))
         (EQUAL (MERGE-ORDERED-INSERT (INSERT-ORDERED (CAR A) B)
                                      C)
                (INSERT-ORDERED (CAR A)
                                (MERGE-ORDERED-INSERT B C))))
|#
;the true induction case (why are the above split up?)
#|
(defthm insert-ordered-remove (IMPLIES
 (AND (RATIONALP (CAR A))
      (RATIONAL-LISTP (CDR A))
      (CONSP A)
      (EQUAL (MERGE-ORDERED-INSERT (MERGE-ORDERED-INSERT (CDR A) B)
                                   C)
             (MERGE-ORDERED-INSERT (CDR A)
                                   (MERGE-ORDERED-INSERT B C)))
      (ACL2-NUMBERP (CADR A))
      (<= (CAR A) (CADR A))
      (ORDEREDP (CDR A))
      (RATIONAL-LISTP B)
      (ORDEREDP B)
      (RATIONAL-LISTP C)
      (ORDEREDP C))
 (EQUAL
      (MERGE-ORDERED-INSERT (INSERT-ORDERED (CAR A)
                                            (MERGE-ORDERED-INSERT (CDR A) B))
                            C)
      (INSERT-ORDERED (CAR A)
                      (MERGE-ORDERED-INSERT (CDR A)
                                            (MERGE-ORDERED-INSERT B C))))))
|#

;sketch of top-level proof starts here

Conjecture 1:
(implies (and (lorp a) (orderedp a) (lorp b) (orderedp b) (lorp c) (orderedp c))
         (equal (merge-ordered-insert (merge-ordered-insert a b) c)
                (merge-ordered-insert a (merge-ordered-insert b c))))

Proof by: Induction on (lorp a)

;contract case (passes ACL2)
(thm (implies (not (lorp a))
         (implies (and (lorp a) (orderedp a) (lorp b) (orderedp b) (lorp c) (orderedp c))
                  (equal (merge-ordered-insert (merge-ordered-insert a b) c)
                         (merge-ordered-insert a (merge-ordered-insert b c))))))

;base case (passes ACL2)
(thm (implies (endp a)
         (implies (and (lorp a) (orderedp a) (lorp b) (orderedp b) (lorp c) (orderedp c))
                  (equal (merge-ordered-insert (merge-ordered-insert a b) c)
                         (merge-ordered-insert a (merge-ordered-insert b c))))))

;;thm about an ordered list's cdr is still ordered
;passes ACL2 but is it useful?
#|
(thm (implies (and (consp a) (lorp a) (orderedp a))
              (orderedp (cdr a))))
|#

;induction case (ACL2 fails with this one initially (counterexamples of a subgoal))
(thm (implies (and (not (endp a))
                   (implies (and (lorp (cdr a)) (orderedp (cdr a)) (lorp b) (orderedp b) (lorp c) (orderedp c))
                  (equal (merge-ordered-insert (merge-ordered-insert (cdr a) b) c)
                         (merge-ordered-insert (cdr a) (merge-ordered-insert b c)))))
         (implies (and (lorp a) (orderedp a) (lorp b) (orderedp b) (lorp c) (orderedp c))
                  (equal (merge-ordered-insert (merge-ordered-insert a b) c)
                         (merge-ordered-insert a (merge-ordered-insert b c))))))
Exportation:
(implies (and (not (endp a))
              (implies (and (lorp (cdr a)) (orderedp (cdr a)) (lorp b) (orderedp b) (lorp c) (orderedp c))
                       (equal (merge-ordered-insert (merge-ordered-insert (cdr a) b) c)
                              (merge-ordered-insert (cdr a) (merge-ordered-insert b c))))
              (lorp a) (orderedp a) (lorp b) (orderedp b) (lorp c) (orderedp c))
         (equal (merge-ordered-insert (merge-ordered-insert a b) c)
                (merge-ordered-insert a (merge-ordered-insert b c)))))
Context:
C1. (lorp a) 
C2. (orderedp a) 
C3. (lorp b) 
C4. (orderedp b) 
C5. (lorp c) 
C6. (orderedp c)
C7. (not (endp a))
C8. (implies (and (lorp (cdr a)) (orderedp (cdr a)) (lorp b) (orderedp b) (lorp c) (orderedp c))
             (equal (merge-ordered-insert (merge-ordered-insert (cdr a) b) c)
                    (merge-ordered-insert (cdr a) (merge-ordered-insert b c))))

Derived Context:
D1. (consp a) {C1, C7 }
D2. (equal (merge-ordered-insert (merge-ordered-insert (cdr a) b) c)
                    (merge-ordered-insert (cdr a) (merge-ordered-insert b c))) {MP, D1, ACL2}

Goal:
(equal (merge-ordered-insert (merge-ordered-insert a b) c)
                (merge-ordered-insert a (merge-ordered-insert b c)))

;professional method proof that seems to work with a potential lemma
Proof:
(merge-ordered-insert (merge-ordered-insert a b) c)
= {def -merge-ordered-insert}
(merge-ordered-insert
  (if (endp a)
    b
    (insert-ordered (car a) (merge-ordered-insert (cdr a) b)))
  c)
= { C7, PL }
(merge-ordered-insert
 (insert-ordered (car a) (merge-ordered-insert (cdr a) b))
 c)
;;need a lemma here about pulling insert-ordered elem out of a merge-ordered
= {lemma insert-with-merging}
(insert-ordered (car a) (merge-ordered-insert (merge-ordered-insert (cdr a) b) c))
= { D2 }
(insert-ordered (car a) (merge-ordered-insert (cdr a) (merge-ordered-insert b c)))
= {lemma insert-with-merging (backwards)}
(merge-ordered-insert (insert-ordered (car a) (cdr a)) (merge-ordered-insert b c))
;need lemma about car-cdr insert-ordered going back to a
= { lemma car-cdr-insert-ordered }
(merge-ordered-insert a (merge-ordered-insert b c))


;this theorm passes ACL2:
Lemma car-cdr-insert-orderd:
(defthm car-cdr-insert-orderd (implies (and (lorp a) (consp a) (orderedp a))
                                      (equal (insert-ordered (car a) (cdr a))
                                             a)))


;;old lemma, simplified into insert-with-merging-2 below
;lemma about insert-ordered being able to be pulled out of a nested merge-ordered.
;Use this lemma to obtain an expression that we can use the induction scheme on.
Lemma insert-with-merging:
(implies (and (lorp a) (orderedp a) (consp a) (lorp b) (orderedp b) (lorp c) (orderedp c))
         (equal (merge-ordered-insert (insert-ordered (car a) (merge-ordered-insert (cdr a) b)) 
                                      c)
                (insert-ordered (car a) (merge-ordered-insert (merge-ordered-insert (cdr a) b) c))))

;better version of insert-with-merging
;acl2 default to proof by induction on (insert-ordered a b) (fails with no counterexamples/fails )
;when hinted to use (lorp b), fails with counterexamples on subgoals
;when hinted to use (orderedp b), pushes a lot of subgoals for proof by induction
;unsure how to go about proving this?
;(lorp c) hard fails
;didn't run 
Lemma insert-with-merging-2:
(defthm insert-with-merge-2 (implies (and (rationalp a) (lorp b) (orderedp b) (lorp c) (orderedp c))
                                     (equal (merge-ordered-insert (insert-ordered a b) c)
                                            (insert-ordered a (merge-ordered-insert b c))))
  :hints (("Goal" :induct (lorp (insert-ordered a b)))))


;what induction scheme to use?
;will have to unfold call to inseert-ordered or a call to merge-ordered-insert
;perhaps merge-ordered-insert
;induct on (lorp (insert-ordered a b))
;possibly on (merge-ordered-insert a b)?
;possibly (tlp c)
;what's the base case? '() or single element?
;pt 1
(if (<= a (car b))
(if (<= a (car (merge-ordered-insert b c)))
(thm (implies (and (rationalp a) (lorp b) (orderedp b) (lorp c) (orderedp c)
              (<= a (car b)) (<= a (car (merge-ordered-insert b c))))
(equal (merge-ordered-insert (cons a b) c) (cons a (merge-ordered-insert b c)))))

;pt2
(if (<= a (car b)))
  (not (if (<= a (car (merge-ordered-insert b c)))))
(equal (merge-ordered-insert (cons a b) c)
(cons (car (merge-ordered-insert b c)) (insert-ordered a (cdr (merge-ordered-insert b c))))))

;try to prove
(thm (implies (and (rationalp a) (lorp b) (orderedp b) (lorp c) (orderedp c)
              (<= a (car b)) (not (<= a (car (merge-ordered-insert b c)))))
(equal (merge-ordered-insert (cons a b) c)
(cons (car (merge-ordered-insert b c)) (insert-ordered a (cdr (merge-ordered-insert b c)))))))

;pt 3
(thm (implies (and (rationalp a) (lorp b) (orderedp b) (lorp c) (orderedp c)
              (not (<= a (car b))) (<= a (car (merge-ordered-insert b c))))
(equal (merge-ordered-insert (cons (car b) (insert-ordered a (cdr b))) c)
(cons a (merge-ordered-insert b c)))))

;pt 4
(thm (implies (and (rationalp a) (lorp b) (orderedp b) (lorp c) (orderedp c)
              (not (<= a (car b))) (not (<= a (car (merge-ordered-insert b c)))))
(equal (merge-ordered-insert (cons (car b) (insert-ordered a (cdr b))) c)
(cons (car (merge-ordered-insert b c)) (insert-ordered a (cdr (merge-ordered-insert b c)))))))



;this still doesn't pass (thm (implies
(and (rationalp a) (lorp b) (orderedp b) (lorp c) (orderedp c)
(<= a (car b))
(not (<= a (car (merge-ordered-insert b c)))))
(equal (car (merge-ordered-insert b c)) (car c)))

