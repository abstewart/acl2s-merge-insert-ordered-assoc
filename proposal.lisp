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
proposal.lisp
Initial project proposal

Authors:
Andrew Briasco-Stewart
briasco-stewart.a@northeastern.edu

Christopher Swagler
swagler.c@northeastern.edu

Steve Liu
liu.steve@northeastern.edu
|#

#| Part II Project Start-up |#

#|

This part of your homework this week will /be/ to come up with your
project proposal/suggestion. You should first read all of the prose
and descriptions for what we're looking for, how we'll assess you at
each stage of this exercise, the due dates for each deliverable, and
look to the schedule for upcoming lectures that may be on topic. After
considering the above, looking and exploring, you should write, here,
below this prose, a two to three paragraph statement including:

- in which of the two general topic areas you intend to work*,

- explain the general background(either the ACL2 code, or
  game/artifact/situation otherwise) that you want to investigate,

- precisely what you want to show,

- that your initial searches revealed no prior art answering this
  question (if you're unclear, explain how yours will differ from
  existing works)

- how you (think you) know that this project is in scope.

|#

;; Together as a group (if you have one) you will make a 15m
;; appointment to meet with either Josh, Ankit, Drew, or me the week
;; of the 22nd-27th of March. I will make myself available at some
;; extra times for people to book appointments; the others you can try
;; to meet during office hours. You will meet with us, and we will
;; work with you on these, to hopefully make sure you have come up
;; with an adequate topic and are set out to explore how to proceed.

;; We will, however, assess this written document that you submit as a
;; stand-alone entry, for both content and grammar/spelling. We will
;; consider this dually here for completion as a part of your
;; homework, and also assess it for quality (as described above) and
;; for meeting the requirements laid out as a part of your overall
;; project grade.

;; * Or if your topic is one of the "none of the above/alternate"
;; options we discussed: that can work too!
(defdata lon (listof nat))

(definec app2 (a :tl b :tl) :tl
  (if (endp a)
      b
    (cons (first a) (app2 (rest a) b))))

(definec orderedp (l :lon) :bool
  (cond
   ((endp (cdr l)) t)
   (t (and (<= (car l) (cadr l)) (orderedp (rest l))))))

(definec merge-ordered (l1 :lon l2 :lon) :lon
  :ic (and (orderedp l1) (orderedp l2))
  :oc (orderedp (merge-ordered l1 l2))
  (cond
   ((and (endp l1) (endp l2)) nil)
   ((endp l1) l2)
   ((endp l2) l1)
   ((< (car l1) (car l2)) (cons (car l1) (merge-ordered (cdr l1) l2)))
   (t (cons (car l2) (merge-ordered l1 (cdr l2))))))

(defthm test1 (IMPLIES (AND (AND (NAT-LISTP B)
                        (NAT-LISTP C)
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

(defthm merge-assoc (implies (and (lonp a) (lonp b) (lonp c) (orderedp a) (orderedp b) (orderedp c))
  (equal (merge-ordered (merge-ordered a b) c) (merge-ordered a (merge-ordered b c)))))

(definec rev2 (x :tl) :tl
  (if (endp x)
      nil
    (app2 (rev2 (rest x)) (list (first x)))))
#|
;;acc version, but acc is the reversed list
(definec merge-ordered* (l1 :lon l2 :lon acc :lon) :lon
  :ic (and (orderedp l1) (orderedp l2))
  :oc (orderedp (merge-ordered* l1 l2 acc))
  (cond
   ((and (endp l1) (endp l2)) (rev2 acc))
   ((endp l1) (rev2 (app2 l2 acc)))
   ((endp l2) (rev2 (app2 l1 acc)))
   ((< (car l1) (car l2)) (merge-ordered* (cdr l1) l2 (cons (car l1) acc)))
   (t (merge-ordered* l1 (cdr l2) (cons (car l2) acc)))))
  |#
