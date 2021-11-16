(define-sort BV () (_ BitVec 2))
(declare-fun pred (BV BV) Bool)
(declare-fun cnd (BV BV BV) Bool)


(assert (exists ((x BV) (y BV)) (pred x y)))
(assert (exists ((x BV) (y BV) (z BV)) (not (cnd x y z))))
(assert (exists ((x BV) (y BV) (z BV)) (cnd x y z)))

(assert (forall ((x BV) (x1 BV) (x2 BV))
                (=> (pred x1 x2)
                    (or (= x x1) (= x x2)))))
(check-sat)
(get-model)
