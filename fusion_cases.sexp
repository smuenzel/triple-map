((V1 _ _) (V2 _ _ _ _) (Node 5 n1 k0 v0 n2))

((V2 _ _ _ _) (V1 _ _) (Node 5 n1 k0 v0 n2))

((V1 _ _) (V3 _ _ _ _ _ _) (Node 6 n1 k0 v0 n2))

((V3 _ _ _ _ _ _) (V1 _ _) (Node 6 n1 k0 v0 n2))

((V2 _ _ _ _)
 (V2 _ _ _ _)
 (Node 6 n1 k0 v0 n2))

((V2 _ _ _ _) (V3 _ _ _ _ _ _) (Node 7 n1 k0 v0 n2))

((V3 _ _ _ _ _ _) (V2 _ _ _ _) (Node 7 n1 k0 v0 n2))

((V3 _ _ _ _ _ _) (V3 _ _ _ _ _ _) (Node 8 n1 k0 v0 n2))

#| Pack into V3 nodes |#
((V2 k11 v11 k1 v1)
 (Node _ (V2 k211 v211 k21 v21) k2 v2 (V1 k22 v22))
 (Node 8 (V3 k11 v11 k1 v1 k0 v0) k211 v211 (V3 k21 v21 k2 v2 k22 v22)))

((V2 k11 v11 k1 v1)
 (Node _ (V1 k21 v21) k2 v2 (V2 k221 v221 k22 v22))
 (Node 8 (V3 k11 v11 k1 v1 k0 v0) k21 v21 (V3 k2 v2 k221 v221 k22 v22)))

((Node _ (V2 k111 v111 k11 v11) k1 v1 (V1 k12 v12))
 (V2 k21 v21 k2 v2)
 (Node 8 (V3 k111 v111 k11 v11 k1 v1) k12 v12 (V3 k0 v0 k21 v21 k2 v2)))

((Node _ (V1 k11 v11) k1 v1 (V2 k121 v121 k12 v12))
 (V2 k21 v21 k2 v2)
 (Node 8 (V3 k11 v11 k1 v1 k121 v121) k12 v12 (V3 k0 v0 k21 v21 k2 v2)))
