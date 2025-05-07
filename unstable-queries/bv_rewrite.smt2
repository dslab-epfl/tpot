(declare-fun addr_A () (_ BitVec 64))
(declare-fun i () (_ BitVec 64))
(declare-fun p () (_ BitVec 64))

(declare-fun addr_B () (_ BitVec 64))

; constrain addr_B
;! this assertion increases solving time from instant to 73s.
(assert (= addr_B
    (bvadd p (bvmul #x000000000000000c i))
))


; Both bases are positive numbers
(assert (bvslt #x0000000000000000 addr_A))
(assert (bvslt #x0000000000000000
   addr_B))


; A and B do not overlap
(assert (bvule (bvadd #x00000000000000c8 addr_A)
   addr_B))


(assert (let
   ; a!1 is the "offset" of the memory access w.r.t. B
   ((a!1 (bvsub (bvadd #x00000000000000c0 addr_A)
                 addr_B)))


   ; the accessed range is within B                    
   (and (bvsle #x0000000000000000 a!1)
        (bvult (bvadd a!1 #x0000000000000004) #x0000000000000010))))

(assert (= addr_B
    (bvadd p (bvmul #x000000000000000c i))
))
(check-sat)