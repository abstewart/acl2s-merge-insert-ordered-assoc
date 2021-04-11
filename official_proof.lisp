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


;;lemma 1
;this theorm passes ACL2:
;Lemma car-cdr-insert-orderd:
;**explanation
(defthm car-cdr-insert-orderd (implies (and (lorp a) (consp a) (orderedp a))
                                      (equal (insert-ordered (car a) (cdr a))
                                             a)))#|ACL2s-ToDo-Line|#


;lemma 2
;Lemma insert-with-merging:
;when skipped this goes through fine
(defthm insert-with-merging (implies (and (rationalp a) (lorp b) (orderedp b) (lorp c) (orderedp c))
                                     (equal (merge-ordered-insert (insert-ordered a b) c)
                                            (insert-ordered a (merge-ordered-insert b c)))))
;:hints (("Goal" :induct (lorp (insert-ordered a b))))
                                     
                                     


;Official theorem trying to prove:
(defthm -merge-ordered-inesrt-assoc 
  (implies (and (lorp a) (orderedp a) (lorp b) (orderedp b) (lorp c) (orderedp c))
           (equal (merge-ordered-insert (merge-ordered-insert a b) c)
                  (merge-ordered-insert a (merge-ordered-insert b c)))))


