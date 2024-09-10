Predicates
pL := (and (< (* $R $R) 0.1) (= $I 0))
p0 := (and (= $R 0) (= $I 0))
pH := (and (> (* $R $R) 0.9) (= $I 0))
Root States 0
Colored Transitions
[1,1](2, 1) -> 0
[2,1](3, 3) -> 1
[2,1](3, 4) -> 2
[3,1](5, 5) -> 3
[3,1](5, 6) -> 4
[pL,1] -> 5
[pH,1] -> 6
