((Empty)
 (Empty)
 (V1 k0 v0))

((V1 k1 v1) (Empty) (V2 k1 v1 k0 v0))

((Empty) (V1 k2 v2) (V2 k0 v0 k2 v2))

((V1 k1 v1)
 (V1 k2 v2)
 (V3 k1 v1 k0 v0 k2 v2))

#| Sensible Cases From Mathematica |#
#| Single Rotation Case M1, Left: |#
#| Double Rotation Case M1, Left: |#
((V2 k11 v11 k1 v1) (Empty) (V3 k11 v11 k1 v1 k0 v0))

#| Single Rotation Case M1, Right: |#
#| Double Rotation Case M1, Right: |#
((Empty) (V2 k21 v21 k2 v2) (V3 k0 v0 k21 v21 k2 v2))

#| Single Rotation Case M2, Left: |#
((V3 k11 v11 k1 v1 k12 v12)
 (Empty)
 (Node 5 (V2 k11 v11 k1 v1) k12 v12 (V1 k0 v0)))

#| Single Rotation Case M2, Right: |#
((Empty)
 (V3 k21 v21 k2 v2 k22 v22)
 (Node 5 (V2 k0 v0 k21 v21) k2 v2 (V1 k22 v22)))

#| Single Rotation Case M3, Left: |#
((Node _ (V3 k111 v111 k11 v11 k112 v112) k1 v1 (V1 k12 v12))
 (V1 k2 v2)
 (Node 8 (V3 k111 v111 k11 v11 k112 v112) k1 v1 (V3 k12 v12 k0 v0 k2 v2)))

#| Single Rotation Case M3, Right: |#
((V1 k1 v1)
 (Node _ (V1 k21 v21) k2 v2 (V3 k221 v221 k22 v22 k222 v222))
 (Node 8 (V3 k1 v1 k0 v0 k21 v21) k2 v2 (V3 k221 v221 k22 v22 k222 v222)))

#| Single Rotation Case M4, Left: |#
((Node _ (Node 5 n111 k11 v11 n112) k1 v1 (V1 k12 v12))
 (V1 k2 v2)
 (Node 9 (Node 5 n111 k11 v11 n112) k1 v1 (V3 k12 v12 k0 v0 k2 v2)))

#| Single Rotation Case M4, Right: |#
((V1 k1 v1)
 (Node _ (V1 k21 v21) k2 v2 (Node 5 n221 k22 v22 n222))
 (Node 9 (V3 k1 v1 k0 v0 k21 v21) k2 v2 (Node 5 n221 k22 v22 n222)))

#| Double Rotation Case M2, Left: |#
((Node _ (V1 k11 v11) k1 v1 (V3 k121 v121 k12 v12 k122 v122))
 (V1 k2 v2)
 (Node 8 (V3 k11 v11 k1 v1 k121 v121) k12 v12 (V3 k122 v122 k0 v0 k2 v2)))

#| Double Rotation Case M2, Right: |#
((V1 k1 v1)
 (Node _ (V3 k211 v211 k21 v21 k212 v212) k2 v2 (V1 k22 v22))
 (Node 8 (V3 k1 v1 k0 v0 k211 v211) k21 v21 (V3 k212 v212 k2 v2 k22 v22)))

#| Double Rotation Case M3, Left: |#
((Node _
   (V1 k11 v11)
   k1
   v1
   (Node _ (V1 k121 v121) k12 v12 (V2 k1221 v1221 k122 v122)))
 (V1 k2 v)
 (Node 9
   (V3 k11 v11 k1 v1 k121 v121)
   k12
   v12
   (Node 5 (V2 k1221 v1221 k122 v122) k0 v0 (V1 k2 v))))

#| Double Rotation Case M3, Right: |#
((V1 k1 v1)
 (Node _
   (Node _ (V2 k2111 v2111 k211 v211) k21 v21 (V1 k212 v212))
   k2
   v2
   (V1 k22 v22))
 (Node 9
   (Node 5 (V1 k1 v1) k0 v0 (V2 k2111 v2111 k211 v211))
   k21
   v21
   (V3 k212 v212 k2 v2 k22 v22)))

#| Double Rotation Case M4, Left: |#
((Node _
   (V1 k11 v11)
   k1
   v1
   (Node _ (V2 k1211 v1211 k121 v121) k12 v12 (V1 k122 v122)))
 (V1 k2 v2)
 (Node 9
   (V3 k11 v11 k1 v1 k1211 v1211)
   k121
   v121
   (Node 5 (V2 k12 v12 k122 v122) k0 v0 (V1 k2 v2))))

#| Double Rotation Case M4, Right: |#
((V1 k1 v1)
 (Node _
   (Node _ (V1 k211 v211) k21 v21 (V2 k2121 v2121 k212 v212))
   k2
   v2
   (V1 k22 v22))
 (Node 9
   (Node 5 (V1 k1 v1) k0 v0 (V2 k211 v211 k21 v21))
   k2121
   v2121
   (V3 k212 v212 k2 v2 k22 v22)))

#| Double Rotation Case M5, Left: |#
((Node _
   (V2 k111 v111 k11 v11)
   k1
   v1
   (Node _ (V2 k1211 v1211 k121 v121) k12 v12 (V1 k122 v122)))
 (V1 k2 v2)
 (Node 10
   (Node 6 (V2 k111 v111 k11 v11) k1 v1 (V2 k1211 v1211 k121 v121))
   k12
   v12
   (V3 k122 v122 k0 v0 k2 v2)))

#| Double Rotation Case M5, Right: |#
((V1 k1 v1)
 (Node _
   (Node _ (V1 k211 v211) k21 v21 (V2 k2121 v2121 k212 v212))
   k2
   v2
   (V2 k221 v221 k22 v22))
 (Node 10
   (V3 k1 v1 k0 v0 k211 v211)
   k21
   v21
   (Node 6 (V2 k2121 v2121 k212 v212) k2 v2 (V2 k221 v221 k22 v22))))

#| Single Rotation Case 1, Left: |#
((Node _ (V1 k11 v11) k1 v1 (V2 k121 v121 k12 v12))
 (Empty)
 (Node 6 (V2 k11 v11 k1 v1) k121 v121 (V2 k12 v12 k0 v0)))

#| Single Rotation Case 1, Right: |#
((Empty)
 (Node _ (V1 k21 v21) k2 v2 (V2 k221 v221 k22 v22))
 (Node 6 (V2 k0 v0 k21 v21) k2 v2 (V2 k221 v221 k22 v22)))
#| Single Rotation Case 2, Right: |#
((Node _ (V2 k111 v111 k11 v11) k1 v1 (V1 k12 v12))
 Empty
 (Node 6 (V2 k111 v111 k11 v11) k1 v1 (V2 k12 v12 k0 v0)))
#| Single Rotation Case 2, Left: |#
(Empty
 (Node _ (V2 k211 v211 k21 v21) k2 v2 (V1 k22 v22))
 (Node 6 (V2 k0 v0 k211 v211) k21 v21 (V2 k2 v2 k22 v22)))
#| Single Rotation Case 3, Left: |#
((Node _ (V2 k111 v111 k11 v11) k1 v1 (V2 k121 v121 k12 v12))
 (Empty)
 (Node 7 (V2 k111 v111 k11 v11) k1 v1 (V3 k121 v121 k12 v12 k0 v0)))

#| Single Rotation Case 3, Right: |#
((Empty)
 (Node _ (V2 k211 v211 k21 v21) k2 v2 (V2 k221 v221 k22 v22))
 (Node 7 (V3 k0 v0 k211 v211 k21 v21) k2 v2 (V2 k221 v221 k22 v22)))

#| Single Rotation Case 4, Left: |#
((Node _ (V3 k111 v111 k11 v11 k112 v112) k1 v1 (V2 k121 v121 k12 v12))
 (Empty)
 (Node 8 (V3 k111 v111 k11 v11 k112 v112) k1 v1 (V3 k121 v121 k12 v12 k0 v0)))

#| Single Rotation Case 4, Right: |#
((Empty)
 (Node _ (V2 k211 v211 k21 v21) k2 v2 (V3 k221 v221 k22 v22 k222 v222))
 (Node 8 (V3 k0 v0 k211 v211 k21 v21) k2 v2 (V3 k221 v221 k22 v22 k222 v222)))

#| Single Rotation Case 5, Left: |#
((Node _ (V3 k111 v111 k11 v11 k112 v112) k1 v1 (V1 k12 v12))
 (Empty)
 (Node 7 (V3 k111 v111 k11 v11 k112 v112) k1 v1 (V2 k12 v12 k0 v0)))

#| Single Rotation Case 5, Right: |#
((Empty)
 (Node _ (V1 k21 v21) k2 v2 (V3 k221 v221 k22 v22 k222 v222))
 (Node 7 (V2 k0 v0 k21 v21) k2 v2 (V3 k221 v221 k22 v22 k222 v222)))

#| Double Rotation Case 1, Left: |#
((Node _ (V1 k11 v11) k1 v1 (V3 k121 v121 k12 v12 k122 v122))
 (Empty)
 (Node 7 (V3 k11 v11 k1 v1 k121 v121) k12 v12 (V2 k122 v122 k0 v0)))

#| Double Rotation Case 1, Right: |#
((Empty)
 (Node _ (V3 k211 v211 k21 v21 k212 v212) k2 v2 (V1 k22 v22))
 (Node 7 (V2 k0 v0 k211 v211) k21 v21 (V3 k212 v212 k2 v2 k22 v22)))
