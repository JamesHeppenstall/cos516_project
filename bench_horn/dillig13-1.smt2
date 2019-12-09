(declare-rel inv (Int Int Bool))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var y0 Int)
(declare-var y1 Int)
(declare-var flag Bool)

(declare-rel fail ())

(rule (=> (and (= x1 2) (= y1 0)) (inv x1 y1 flag)))

(rule (=> 
    (and 
        (inv x0 y0 flag)
        (or 
            (and flag (= x1 (+ x0 4)) (= y1 y0))
            (and (not flag) (= x1 (+ x0 2)) (= y1 (+ y0 1)))
        )
    )
    (inv x1 y1 flag)
  )
)

(rule (=> (and (inv x1 y1 flag) (not (= y1 0)) (not (= x1 (+ 2 (* 2 y1))))) fail))

(query fail :print-certificate true)