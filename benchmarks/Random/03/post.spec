Numbers
c0 := (0 + 0 * A(1/8) + -1 * A(2/8) + 0 * A(3/8)) / (V2 ^ 2)
c1 := (0 + 0 * A(1/8) + 0 * A(2/8) + 0 * A(3/8)) / (V2 ^ 0)
c2 := (0 + 0 * A(1/8) + 1 * A(2/8) + 0 * A(3/8)) / (V2 ^ 2)
Transitions
[1](1, 2) -> 0
[2](3, 4) -> 1
[2](5, 6) -> 2
[3](7, 7) -> 3
[3](7, 8) -> 4
[3](8, 7) -> 6
[3](9, 8) -> 5
[c0] -> 8
[c1] -> 7
[c2] -> 9