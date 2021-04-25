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

#|
project_work.lisp
All of our work leading up to our successful proof

Authors:
Andrew Briasco-Stewart
briasco-stewart.a@northeastern.edu

Christopher Swagler
swagler.c@northeastern.edu

Steve Liu
liu.steve@northeastern.edu
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;******************** Initial Work ***********************;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
Summary: After our initial proposal, this was the start of our work. We
began with the function definitions suggested in the proposal and observed
the ACL2 output that seemingly spun forever. At this point, we were trying to
see where and why the ACL2 proof did not terminate. We tried deriving the
following possible lemmas from the ACL2 induction schemes.

End result: We were unable to make progress with our current function
definitions and decided to switch gears to using merge-ordered-insert
as opposed to merge-ordered
|#
(defdata lor (listof rational))

(definec orderedp (l :lor) :bool
  (cond
   ((endp (cdr l)) t)
   (t (and (<= (car l) (cadr l)) (orderedp (rest l))))))

(definec merge-ordered (l1 :lor l2 :lor) :lor
  :ic (and (orderedp l1) (orderedp l2))
  :oc (orderedp (merge-ordered l1 l2))
  (cond
   ((endp l1) l2)
   ((endp l2) l1)
   ((< (car l1) (car l2)) (cons (car l1) (merge-ordered (cdr l1) l2)))
   (t (cons (car l2) (merge-ordered l1 (cdr l2))))))
;; These next two functions were created as a result of the above definitions
;; not gaining any considerable progress. More to be explored in the next section
;insert-ordered
(definec insert-ordered (elem :rational l :lor) :lor
  (cond
   ((endp l) (list elem))
   ((<= elem (car l)) (cons elem l))
   (t (cons (car l) (insert-ordered elem (cdr l))))))

;;merging with insertion
(definec merge-ordered-insert (l1 :lor l2 :lor) :lor
  :ic (and (orderedp l1) (orderedp l2))
  :oc (orderedp (merge-ordered l1 l2))
  (if (endp l1)
    l2
    (insert-ordered (car l1) (merge-ordered-insert (cdr l1) l2))))


;; Trying to develop smaller lemmas

(defthm cons-smaller-is-ordered (implies (and (rationalp a) (lorp b) (orderedp b) (consp b) (< a (car b)))
                                      (orderedp (cons a b))))

(defthm merge-assoc (implies (and (lorp a) (lorp b) (lorp c) (orderedp a) (orderedp b) (orderedp c))
  (equal (merge-ordered (merge-ordered a b) c) (merge-ordered a (merge-ordered b c))))
  )

;;equality of merge-ordered-insert and merge-ordered
(defthm merge-insert (implies (and (lorp a) (lorp b) (orderedp a) (orderedp b))
  (equal (merge-ordered a b) (merge-ordered-insert a b))))

;;proof in merge-ordered-insert form
(defthm merge-assoc (implies (and (lorp a) (lorp b) (lorp c) (orderedp a) (orderedp b) (orderedp c))
  (equal (merge-ordered-insert (merge-ordered a b) c) (merge-ordered-insert a (merge-ordered b c))))
  )

;(set-gag-mode nil)

;possible lemmas
;commutative
(defthm merge-ordered-comm (implies (and (lorp a) (lorp b) (orderedp a) (orderedp b))
                                    (equal (merge-ordered a b) (merge-ordered b a)))
  :hints (("Goal" :induct (lorp a))))

;infin spins
(defthm equal-first-swap (implies (and (rationalp a) (lorp b) (lorp c) (orderedp (cons a b)) (orderedp (cons a c)))
  (equal (merge-ordered (cons a b) (cons a c)) (merge-ordered (cons a c) (cons a b)))))

;proof
#|
(defthm merge-assoc (implies (and (lorp a) (lorp b) (lorp c) (orderedp a) (orderedp b) (orderedp c))
  (equal (merge-ordered (merge-ordered a b) c) (merge-ordered a (merge-ordered b c))))
  )
|#

;this is where it first gets stuck for proving our main theorem
(thm (IMPLIES (AND (AND (RATIONAL-LISTP B)
                   (RATIONAL-LISTP C)
                   (ORDEREDP B)
                   (ORDEREDP C))
              (NOT (AND (ENDP B) (ENDP C)))
              (NOT (ENDP B))
              (NOT (ENDP C))
              (<= (CAR C) (CAR B))
              (EQUAL (MERGE-ORDERED (MERGE-ORDERED (CDR A) B)
                                    (CDR C))
                     (MERGE-ORDERED (CDR A)
                                    (MERGE-ORDERED B (CDR C))))
              (RATIONAL-LISTP A)
              (RATIONAL-LISTP B)
              (RATIONAL-LISTP C)
              (ORDEREDP A)
              (ORDEREDP B)
              (ORDEREDP C))
         (EQUAL (MERGE-ORDERED (MERGE-ORDERED A B) C)
                (MERGE-ORDERED A (MERGE-ORDERED B C)))))

;this is the first complex induction it tries to prove
(defthm test1 (IMPLIES (AND (AND (RATIONAL-LISTP B)
                        (RATIONAL-LISTP C)
                        (ORDEREDP B)
                        (ORDEREDP C))
                   (NOT (AND (ENDP B) (ENDP C)))
                   (NOT (ENDP B))
                   (NOT (ENDP C))
                   (< (CAR B) (CAR C))
                   (let ((a a) (b (cdr b)) (c c))
                    (implies (and (lonp a) (lonp b) (lonp c) (orderedp a) (orderedp b) (orderedp c))
  (equal (merge-ordered (merge-ordered a b) c) (merge-ordered a (merge-ordered b c))))))
              (implies (and (lonp a) (lonp b) (lonp c) (orderedp a) (orderedp b) (orderedp c))
  (equal (merge-ordered (merge-ordered a b) c) (merge-ordered a (merge-ordered b c))))))

;;our property we're trying to prove
(defthm merge-assoc (implies (and (lorp a) (lorp b) (lorp c) (orderedp a) (orderedp b) (orderedp c))
  (equal (merge-ordered (merge-ordered a b) c) (merge-ordered a (merge-ordered b c)))))


;sketch of proof:
;*acl2 can't rewrite the given proof before it tries to induct
;
;possible property, might be helpful
;a is a rational, b is a lor, c is a lor
;(equal (merge-ordered (cons a b) (cons a c)) (merge-ordered (cons a c) (cons a b)))
(defthm equal-first-swap (implies (and (rationalp a) (lorp b) (lorp c) (orderedp (cons a b)) (orderedp (cons a c)))
  (equal (merge-ordered (cons a b) (cons a c)) (merge-ordered (cons a c) (cons a b)))))

;merge-ordered-comm
(defthm merge-ordered-comm (implies (and (lorp a) (lorp b) (orderedp a) (orderedp b))
                                    (equal (merge-ordered a b) (merge-ordered b a))))

(defthm merge-assoc (implies (and (lorp a) (lorp b) (lorp c) (orderedp a) (orderedp b) (orderedp c))
  (equal (merge-ordered (merge-ordered a b) c) (merge-ordered a (merge-ordered b c)))))

;proof by induction on ?


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;*********************** New Functions ****************************;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
Summary: We decided to start fresh with our new function definitions, using
merge-ordered-insert as our primary function instead of merge-ordered. Located
toward the end of this section, we began sketching the proof by hand to see
if any possible lemmas would arise. We were able to derive two distinct lemmas
that we deemed necessary, one of which passed trivially but the other would
fail after some time. The main work in this section was trying to use the
output failure from the lemma to find smaller lemmas to help it pass.

End result: We hand-sketched our proof and determined necessary lemmas to prove.
One of the lemmas needed more to pass, so we tried separating the cases and
providing smaller lemmas in the hope that it would pass. At the end of this,
we were definitely on track, but still stuck on that sub-lemma.
|#

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
(equal (merge-ordered-insert (cons a b) c) (cons a (merge-ordered-insert b c)))))

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
;will have to unfold call to insert-ordered or a call to merge-ordered-insert
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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;****************** Work with Professor *************************;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
Summary: We presented our progress to the professor and showed the sub-lemma
that we needed help proving. We ended up delving deep into sub-cases and trying
to prove car-cdr properties of the lemma at a basic level. To our surprise,
even the seemingly most basic cases would not pass.

End result: The work done in this section was not incredibly helpful for us
solving the final proof. We dove deep into a rabbit hole of issues that
seemingly had no end. A positive from this portion, however, was that we
should take a step back and try to attack the problem from a different angle.
|#

;; smallest element in a list
;; (definec smallest x ls)

(implies (and (lorp (cons x y))
              (orderedp (cons x y))
              (lorp l2)
              (orderedp l2)
              (smaller-than-all x l2))
         (equal x (car (merge-ordered-insert (cons x y) l2))))

#| ------ |#

(defthm insert-with-merge-2 (implies (and (rationalp a) (lorp b) (orderedp b) (lorp c) (orderedp c))
                                     (equal (merge-ordered-insert (insert-ordered a b) c)
                                            (insert-ordered a (merge-ordered-insert b c))))
  :hints (("Goal" :induct (lorp (insert-ordered a b)))))

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

;mergeing ordered with repeated calls to insert-ordered
;if add (orderedp l1) to the :ic, ACL2 can't prove the function contracts
(definec merge-ordered-insert (l1 :lor l2 :lor) :lor
  :ic (orderedp l2)
  :oc (orderedp (merge-ordered-insert l1 l2))
  (if (endp l1)
    l2
    (insert-ordered (car l1) (merge-ordered-insert (cdr l1) l2))))

;; smallest element in a list
;; (definec smallest x ls)


(implies (and (lorp (cons x y))
              (orderedp (cons x y))
              (lorp l2)
              (orderedp l2)
              (smaller-than-all x l2))
         (equal x (car (merge-ordered-insert (cons x y) l2))))

(implies (and (lorp (cons y z))
              (rational x)
              (orderedp (cons y z))
              (<= x y))
         (equal x (car (insert-ordered x (cons y z)))))

;;lemma insert with merging
(implies (and (rationalp a) (lorp b) (orderedp b) (lorp c) (orderedp c))
         (equal (merge-ordered-insert (insert-ordered a b) c) (insert-ordered a (merge-ordered-insert b c))))
;what to prove
(equal (merge-ordered-insert (insert-ordered a b) c) (insert-ordered a (merge-ordered-insert b c)))

;;break up the lists into car and cdr
(implies
 (and (rationalp a)
      (lorp (cons x y)) (orderedp (cons x y))
      (lorp (cons w v)) (orderedp (cons w v))
      (<= a x)
      (< (car (merge-ordered-insert (cons x y) (cons w v))) a))
 (equal (car (merge-ordered-insert (cons x y) (cons w v))) w))

;;expand the above into two cases
(implies
 (and (lorp (cons x y)) (orderedp (cons x y))
      (lorp (cons w v)) (orderedp (cons w v)))
 (or (and (<= x w)
          (equal (merge-ordered-insert (cons x y) (cons w v))
                 (cons x (merge-ordered-insert y (cons w v)))))
     (and (> x w)
          (equal (merge-ordered-insert (cons x y) (cons w v))
                 (cons w (merge-ordered-insert (cons x y) v))))))
;try to thm one half of the above, breaks
(thm
 (implies
  (and (lorp (cons x y)) (orderedp (cons x y))
       (lorp (cons w v)) (orderedp (cons w v))
       (<= x w))
  (equal (merge-ordered-insert (cons x y) (cons w v))
         (cons x (merge-ordered-insert y (cons w v))))))

;somewhat broken,
#|
(if (<= a (car b))
    (if (<= a (car (merge-ordered-insert b c)))
        (equal (merge-ordered-insert (cons a b) c)) (cons (car c) (merge-ordered-insert (cons a b) (cdr c)))
        nil)
  nil)
|#
(if (<= a (car b))
    (if (<= a (car (merge-ordered-insert b c)))
        (equal (merge-ordered-insert (cons a b) c)) (cons a (merge-ordered-insert (cons a b) (cdr c)))
        nil)
  nil)


;4 part breakdown of things to prove, depending on the value of a relative to car b and car c
(if (<= a (car b))
    (if (<= a (car (merge-ordered-insert b c)))
        (equal (merge-ordered-insert (cons a b) c) (cons a (merge-ordered-insert b c)))
      (equal (merge-ordered-insert (cons a b) c)
             (cons (car (merge-ordered-insert b c)) (insert-ordered a (cdr (merge-ordered-insert b c))))))
  (if (<= a (car (merge-ordered-insert b c)))
      (equal (merge-ordered-insert (cons (car b) (insert-ordered a (cdr b))) c)
             (cons a (merge-ordered-insert b c)))
      (equal (merge-ordered-insert (cons (car b) (insert-ordered a (cdr b))) c)
          (cons (car (merge-ordered-insert b c)) (insert-ordered a (cdr (merge-ordered-insert b c))))))
  )


(equal (merge-ordered-insert (cond
                              ((<= a (car b)) (cons a b))
                              (t (cons (car b) (insert-ordered a (cdr b)))))
                             c)
       (cond
        ((<= a (car (merge-ordered-insert b c))) (cons a (car (merge-ordered-insert b c))))
        (t (cons (car (merge-ordered-insert b c)) (insert-ordered a (cdr (merge-ordered-insert b c)))))))

(cond
   ((endp (merge-ordered-insert b c)) (list a))
   ((<= a (car (merge-ordered-insert b c))) (cons a (car (merge-ordered-insert b c))))
   (t (cons (car (merge-ordered-insert b c)) (insert-ordered a (cdr (merge-ordered-insert b c))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;************************* Final Testing ****************************;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
Summary: We were finally able to prove our main theorem (and sub-theorems)
in this section. We took a different approach in our testing by utilizing
skip-proofs to ensure the steps we were taking would still lead us on track
to prove our final goal. We ultimately found three sub goals, two of which
passed rather trivially, but the third gave rise to another lemma that
was easy for us to spot.

End result: Once we proved this lemma, we were able to fold back
up the previous lemmas to ultimately prove our main theorem. We also dabbled
in other potential properties and found that commutativity could also be
proven with these other sub-lemmas.
|#

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


;;lemma 1
;this theorm passes ACL2:
;Lemma car-cdr-insert-orderd:
;**explanation
(defthm car-cdr-insert-orderd (implies (and (lorp a) (consp a) (orderedp a))
                                      (equal (insert-ordered (car a) (cdr a))
                                             a)))
;(set-gag-mode nil)
;*1.1
(defthm pt1.1
  (IMPLIES (AND (RATIONALP (CAR B))
                (RATIONAL-LISTP C)
                (ORDEREDP C)
                (CONSP B)
                (RATIONALP A)
                (NOT (CDR B))
                (< (CAR B) A))
           (EQUAL (INSERT-ORDERED (CAR B)
                                  (INSERT-ORDERED A C))
                  (INSERT-ORDERED A (INSERT-ORDERED (CAR B) C)))))

;*1.2
(defthm pt1.2
  (IMPLIES (AND (RATIONALP (CAR B))
                (NOT (CDR B))
                (RATIONAL-LISTP C)
                (ORDEREDP C)
                (CONSP B)
                (RATIONALP A)
                (<= (CAR B) 0)
                (< (CAR B) A))
           (EQUAL (INSERT-ORDERED (CAR B)
                                  (INSERT-ORDERED A C))
                  (INSERT-ORDERED A (INSERT-ORDERED (CAR B) C)))))

;1.3
;induction scheme is what??
(defthm insert-ordered-assoc
  (implies (and (rationalp a) (rationalp b) (lorp c) (orderedp c))
           (equal (insert-ordered a (insert-ordered b c))
                  (insert-ordered b (insert-ordered a c)))))
 (defthm pt1.3
   (IMPLIES
    (AND (RATIONALP (CAR B))
         (RATIONAL-LISTP (CDR B))
         (RATIONAL-LISTP C)
         (ORDEREDP C)
         (CONSP B)
         (EQUAL (MERGE-ORDERED-INSERT (INSERT-ORDERED A (CDR B))
                                      C)
                (INSERT-ORDERED A (MERGE-ORDERED-INSERT (CDR B) C)))
         (RATIONALP A)
         (ACL2-NUMBERP (CADR B))
         (<= (CAR B) (CADR B))
         (ORDEREDP (CDR B))
         (< (CAR B) A))
    (EQUAL (INSERT-ORDERED (CAR B)
                           (INSERT-ORDERED A (MERGE-ORDERED-INSERT (CDR B) C)))
           (INSERT-ORDERED A
                           (INSERT-ORDERED (CAR B)
                                           (MERGE-ORDERED-INSERT (CDR B) C))))))

;lemma 2
;Lemma insert-with-merging:
;when skipped this goes through fine
;*1
;gives 3 troublesome things, *1.1-*1.3
(defthm insert-with-merging (implies (and (rationalp a) (lorp b) (orderedp b) (lorp c) (orderedp c))
                                     (equal (merge-ordered-insert (insert-ordered a b) c)
                                            (insert-ordered a (merge-ordered-insert b c)))))
;:hints (("Goal" :induct (lorp (insert-ordered a b))))

;Official theorem trying to prove:
(defthm -merge-ordered-inesrt-assoc
  (implies (and (lorp a) (orderedp a) (lorp b) (orderedp b) (lorp c) (orderedp c))
           (equal (merge-ordered-insert (merge-ordered-insert a b) c)
                  (merge-ordered-insert a (merge-ordered-insert b c)))))

;try commutitativity? YES!
(defthm -merge-ordered-inesrt-comm
  (implies (and (lorp a) (orderedp a) (lorp b) (orderedp b))
           (equal (merge-ordered-insert a b)
                  (merge-ordered-insert b a))))

;semi-group? (to-try) (investivage)

;;other properties to try and prove?
;no inverse,
;semi-group?
;others
