(set-logic UFBV)

(define-sort BV () (_ BitVec 32))
(declare-const rokx BV)
(declare-const roky BV)
(declare-const roa (_ BitVec 1))
(declare-const rody BV)
(declare-const rodx BV)
(declare-const rtkx BV)
(declare-const rtky BV)
(declare-const rta (_ BitVec 1))

(simplify (forall ((hx BV) (hy BV) (gx BV) (gy BV))
  (=> (= hx rokx) (= hy roky)
      (and
        (=> (= roa #b0)
            (=> (= rodx rtkx) (= gy rtky)
                (and (=> (= rta #b0) (= (= roa #b1) (= rta #b1)))
                     (=> (= rta #b1) (= (= roa #b1) (= rta #b1))))))


        (=> (= roa #b1)
            (=> (= gx rtkx) (= rody rtky)
                (and (=> (= rta #b0) (= (= roa #b1) (= rta #b1)))
                     (=> (= rta #b1) (= (= roa #b1) (= rta #b1))))))))))
