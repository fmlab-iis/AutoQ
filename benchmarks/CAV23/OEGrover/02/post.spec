Predicates
p1 := (and (< (* $R $R) (* aR aR)) (= $I 0))
p2 := (and (= $R 0) (= $I 0))
p3 := (and (> (* $R $R) (* bR bR)) (= $I 0))
Root States 0
Colored Transitions
[1,1](2, 1) -> 0
[2,1](3, 3) -> 1
[2,1](3, 4) -> 2
[3,1](5, 6) -> 3
[3,1](5, 7) -> 4
[p2,1] -> 5
[p1,1] -> 6
[p3,1] -> 7