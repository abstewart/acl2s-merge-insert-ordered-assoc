
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



