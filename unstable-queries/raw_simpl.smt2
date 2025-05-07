(declare-fun tpot_bv2int ((_ BitVec 64)) Int)

(declare-fun f ((_ BitVec 8)) Int)

(declare-fun addr_pool () (_ BitVec 64))
(declare-fun pool () (Array Int (_ BitVec 8)))

(declare-fun addr_block () (_ BitVec 64))
(declare-fun block () (Array Int (_ BitVec 8)))

(declare-fun offset () Int)

(assert 
   (let ((a!12 (f (select pool 2) ))
         (a!16 (f (select pool 3) )))
   (< a!12 a!16)))

(assert
  (= 0 (rem (tpot_bv2int addr_block) 4096)))

(assert (let ((a!1 (concat (select block 3)
                   (concat (select block 2)
                           (concat (select block 1)
                                   (select block 0))))))
(let ((a!2 (concat (select block 6)
                   (concat (select block 5)
                           (concat (select block 4) a!1)))))
  (= (concat (select block 7) a!2)
     addr_pool))))

(assert (= offset 
(- (* 4096 (div (tpot_bv2int addr_block) 
                4096))
   (+ (tpot_bv2int addr_block)
               ))
))

(assert
(let ((a!14 offset))
(let ((a!15 (concat (select block (+ a!14 1))
                    (select block (+ a!14 0))))
      (a!23 (select block (+ 8 (+ a!14 0)))))
(let ((a!16 (concat (select block (+ a!14 2))
                    a!15)))
(let ((a!17 (concat (select block (+ a!14 3))
                    a!16)))
(let ((a!18 (concat (select block (+ a!14 4))
                    a!17)))
(let ((a!19 (concat (select block (+ a!14 5))
                    a!18)))
(let ((a!20 (concat (select block (+ a!14 6))
                    a!19)))
(let ((a!21 (concat (select block (+ a!14 7))
                    a!20)))
(let ((a!22 (- (tpot_bv2int a!21) (tpot_bv2int addr_pool))))
(let ((a!39 
      ; Adding more stores blows up the time to solve... Maybe this should be a graph.
      ; I suppose adding more selects, too.
      ; Removing selects/stores and turning them into single-byte reduced 9secs to 2secs. Would be good to plot.
      (store pool a!22 #x00)
                   ))

(let ((a!51 (f (select a!39 3)))
      (a!55 (f (select a!39 2))))
  (not (< a!55 a!51 ))))))))))))))
(check-sat)