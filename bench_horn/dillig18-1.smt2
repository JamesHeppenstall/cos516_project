(declare-rel inv (Int Int Bool))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var y0 Int)
(declare-var y1 Int)
(declare-var flag Bool)

(declare-rel fail ())

(rule (=> (and (= x1 0) (= y1 0)) (inv x1 y1 flag)))

(rule (=> 
    (and 
        (inv x0 y0 flag)
        (< x0 100)
        (= y1 (ite flag (+ y0 1) y0))
        (= x1 (+ x0 1))
    )
    (inv x1 y1 flag)
  )
)

(rule (=> (and (inv x1 y1 flag) (>= x1 100) flag (not (= y1 100))) fail))

(query fail :print-certificate true)