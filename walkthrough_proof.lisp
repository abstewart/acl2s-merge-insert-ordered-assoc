;;Our main theorem to prove:
(defthm -merge-ordered-insert-assoc 
  (implies (and (lorp a) (orderedp a) (lorp b) (orderedp b) (lorp c) (orderedp c))
           (equal (merge-ordered-insert (merge-ordered-insert a b) c)
                  (merge-ordered-insert a (merge-ordered-insert b c)))))

;;Our Professional method writing

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

;induction case (ACL2 fails with this one initially with counterexamples on a subgoal (**check)
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
D1. (consp a) {C1, C7}
D2. (equal (merge-ordered-insert (merge-ordered-insert (cdr a) b) c)
                    (merge-ordered-insert (cdr a) (merge-ordered-insert b c))) {MP, D1, ACL2}

Goal:
(equal (merge-ordered-insert (merge-ordered-insert a b) c)
                (merge-ordered-insert a (merge-ordered-insert b c)))

;professional method sketch where we assume lemmas that don't exist yet
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
;;need a lemma here about pulling insert-ordered elem out of a call to merge-ordered-insert
= {lemma insert-with-merging} ;;Lemma 1.2
(insert-ordered (car a) (merge-ordered-insert (merge-ordered-insert (cdr a) b) c))
= { D2 }
(insert-ordered (car a) (merge-ordered-insert (cdr a) (merge-ordered-insert b c)))
= {lemma insert-with-merging (use backwards)}
(merge-ordered-insert (insert-ordered (car a) (cdr a)) (merge-ordered-insert b c))
;need lemma about car-cdr insert-ordered going back to 'a'
= { lemma car-cdr-insert-ordered } ;;Lemma 1.1
(merge-ordered-insert a (merge-ordered-insert b c))


;;The above proof spawns two 1st order Lemmas:

;;Lemma 1.1, car-cdr-insert-ordered
;;This theorem passes ACL2s as-is
(defthm car-cdr-inseert-ordered
  (implies (and (lorp a) (consp a) (orderedp a))
	   (equal (insert-ordered (car a) (cdr a))
		  a)))

;;Lemma 1.2, insert-with-merging
;;This Lemma does not pass ACL2 (Fails with counterexamples on a subgoal) (**Check)
(defthm insert-with-merging
  (implies (and (rationalp a) (lorp b) (orderedp b) (lorp c) (orderedp c))
	   (equal (merge-ordered-insert (insert-ordered a b) c)
		  (insert-ordered a (merge-ordered-insert b c)))))

;;When the above lemma fails in ACL2s, it provides 3 key checkpoints, creating our 3 2nd order Lemmas

;;Lemma 2.1
;;This lemma passes ACL2s when written as a seperate lemma, go figure
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

;;Lemma 2.2
;;This lemma passes ACL2s when written as a seperate lemma, go figure
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


;;Lemma 2.3
;;This Lemma doesn't pass ACL2 on its own, (** Check why)
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

;;When looking at the above theorem, it appears as though what ALC2s is trying to prove is
;;If the calls to insert-ordered can be in either order.
;;Since Merge-ordered-insert is defined to produce an ordered list,
;;we generalize to our single 3rd order lemma

;;Lemma 3.1
(defthm insert-ordered-assoc
  (implies (and (rationalp a) (rationalp b) (lorp c) (orderedp c))
           (equal (insert-ordered a (insert-ordered b c))
                  (insert-ordered b (insert-ordered a c)))))

;;With the above lemma, all previous lemmas are now accepted by ACL2s,
;;and our main theorem is accepted as well.


