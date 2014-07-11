(set-option :auto-config false)
(set-option :smt.mbqi false)
(declare-sort B)
(declare-sort Fuel)
(declare-fun succ (Fuel) Fuel)
(declare-const zero Fuel)
(declare-const fuel Fuel)
(declare-datatypes () ((Lst nl (con (proj_con_0 B) (proj_con_1 Lst)))))
(declare-fun app (Fuel Lst Lst) Lst)
(declare-fun rev (Fuel Lst) Lst)
(declare-fun xs () B)
(declare-fun xs2 () Lst)

(assert (forall ((n Fuel) (us Lst)) (! (= (rev (succ n) us) (rev n us)) :pattern ((rev (succ n) us)))))
(assert (forall ((n Fuel) (us Lst) (vs Lst)) (! (= (app (succ n) us vs) (app n us vs)) :pattern ((app (succ n) us vs)))))


;; REV DEF
(assert
   (forall ((n Fuel) (x B) (xs3 Lst))
;           (! (= (rev (succ n) (con x xs3)) (app (succ n) (rev n xs3) (con x nl)))
           (! (= (rev (succ n) (con x xs3)) (app n (rev n xs3) (con x nl)))
              :pattern ((rev (succ n) (con x xs3))))))
(assert (forall ((n Fuel)) (! (= (rev (succ n) nl) nl)
                              :pattern (rev (succ n) nl)
                              )))

;; APP DEF
(assert
   (forall
      ((n Fuel) (ys Lst) (x2 B) (xs4 Lst))
        (! (= (app (succ n) (con x2 xs4) ys) (con x2 (app n xs4 ys)))
         :pattern (app (succ n) (con x2 xs4) ys))
        ))
(assert (forall ((n Fuel) (ys Lst)) (! (= (app (succ n) nl ys) ys)
                              :pattern ((app (succ n) nl ys)))))


;; app/rev homomorphism
(assert
   (forall
      ((n Fuel) (xs5 Lst) (ys2 Lst))
        (! (= (app (succ n) (rev (succ n) xs5) (rev (succ n) ys2)) (rev n (app n ys2 xs5)))
         :pattern ((app (succ n) (rev (succ n) xs5) (rev (succ n) ys2)))
        )))
(assert
   (forall
      ((n Fuel) (xs5 Lst) (ys2 Lst)) (! (= (app n (rev n xs5) (rev (succ n) ys2)) (rev (succ n) (app (succ n) ys2 xs5)))
                               :pattern ((rev (succ n) (app (succ n) ys2 xs5)))
                            )))

;; app assoc
(assert
   (forall
      ((n Fuel) (xs5 Lst) (ys2 Lst) (zs Lst))
      (! (= (app (succ n) (app (succ n) xs5 ys2) zs)
            (app n xs5 (app n ys2 zs)))
           :pattern ((app (succ n) (app (succ n) xs5 ys2) zs))
      )))

;; app assoc
(assert
   (forall
      ((n Fuel) (xs5 Lst) (ys2 Lst) (zs Lst))
      (! (= (app n (app n xs5 ys2) zs)
            (app (succ n) xs5 (app (succ n) ys2 zs)))
           :pattern ((app (succ n) xs5 (app (succ n) ys2 zs)))
      )))

;; app rid
(assert (forall ((n Fuel) (xs5 Lst))
                (! (= (app (succ n) xs5 nl) xs5)
                :pattern ((app (succ n) xs5 nl))
                )))

;; IH
(assert (forall ((n Fuel)) (! (= (rev (succ n) (rev (succ n) xs2)) xs2)
                            :pattern ((rev (succ n) (rev (succ n) xs2)))
                            )))
;; IC
(assert (not (= (rev fuel (rev fuel (con xs xs2))) (con xs xs2))))

(assert (= fuel (succ (succ (succ (succ (succ zero)))))))
;; (assert (= fuel (succ zero))) ;; timeout
(check-sat)

