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

;this is where it first gets stuck
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


;proof by induction on (
;






