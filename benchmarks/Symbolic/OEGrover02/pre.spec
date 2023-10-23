Numbers
c0 := 0
a
b
Transitions
[1](2, 1) -> 0
[2](3, 3) -> 1
[2](3, 4) -> 2
[3](5, 6) -> 3
[3](5, 7) -> 4
[c0] -> 5
[a] -> 6
[b] -> 7
Constraints
(declare-fun aR () Real)(declare-fun aI () Real)(declare-fun bR () Real)(declare-fun bI () Real)
(assert (> (* 3 aR) bR))(assert (> aR 0))(assert (> bR 0))(assert (= aI 0))(assert (= bI 0))