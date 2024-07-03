#!/usr/bin/python3
from typing import Optional, Any


context = """Numbers
c0 := 0
c1 := 1
Colored Transitions
"""


def tr(top: int, bot: list[int], sym: Any, color: set[int]) -> str:
    tag = sum(1 << (c-1) for c in color)
    bott = ",".join(map(str, bot))
    if bott:
        bott = f"({bott})"

    return f"[{sym},{tag}]{bott} -> {top}"


def gen_toff_prespec(n: int, last_is_one: bool = True):
    def q(lv: int, x: Optional[str] = None) -> int:
        ind = -1
        if x is None:
            ind = 2*lv
        elif x == "0":
            ind = 2*lv - 1
        return ind

    trans: list[str] = [
        # level 1
        tr(q(0), [q(1, "0"), q(1)], 1, {1}),
        tr(q(0), [q(1), q(1, "0")], 1, {2}),
    ]
    last_bot = [q(2*n, "0"), q(2*n)] if last_is_one else [q(2*n), q(2*n, "0")]

    # level 2 to 2n-1
    for i in range(2, 2*n, 2):
        trans.extend([
            # level i
            tr(q(i-1), [q(i), q(i, "0")], i, {1}),
            tr(q(i-1), [q(i, "0"), q(i)], i, {2}),
            tr(q(i-1, "0"), [q(i, "0"), q(i, "0")], i, {1, 2}),
            # level i+1
            tr(q(i), [q(i+1), q(i+1, "0")], i+1, {1}),
            tr(q(i, "0"), [q(i+1, "0"), q(i+1, "0")], i+1, {1}),
        ])
    trans.extend([
        # level 2n
        tr(q(2*n-1), last_bot, 2*n, {1}),
        tr(q(2*n-1, "0"), [q(2*n, "0"), q(2*n, "0")], 2*n, {1}),
        # leafs
        tr(q(2*n), [], "c1", {1}),
        tr(q(2*n, "0"), [], "c0", {1}),
    ])

    return context + "\n".join(trans)


def gen_toff_postspec(n: int, last_is_one: bool) -> str:
    def q(lv: int, x: Optional[str] = None) -> int:
        if x == "T":  # even or none
            ind = 3*lv
        elif (x == "F") or (x is None):  # odd or last
            ind = 3*lv - 1
        else:  # zero
            ind = 3*lv - 2
        return ind
    trans: list[str] = [
        # level 1
        tr(q(0, "T"), [q(1, "F"), q(1, "0")], 1, {1}),
        tr(q(0, "T"), [q(1, "0"), q(1, "T")], 1, {2}),
    ]
    # level 2 to 2n-1
    for i in range(2, 2*n, 2):
        trans.extend([
            # level i
            tr(q(i-1, "T"), [q(i, "F"), q(i, "0")], i, {1}),
            tr(q(i-1, "T"), [q(i, "0"), q(i, "T")], i, {2}),
            tr(q(i-1, "F"), [q(i, "F"), q(i, "0")], i, {1}),
            tr(q(i-1, "F"), [q(i, "0"), q(i, "F")], i, {2}),
            tr(q(i-1, "0"), [q(i, "0"), q(i, "0")], i, {1, 2}),
            # level i+1
            tr(q(i, "T"), [q(i+1, "T"), q(i+1, "0")], i+1, {1}),
            tr(q(i, "F"), [q(i+1, "F"), q(i+1, "0")], i+1, {1}),
            tr(q(i, "0"), [q(i+1, "0"), q(i+1, "0")], i+1, {1}),
        ])
    last_bot = [q(2*n, "0"), q(2*n)] if last_is_one else [q(2*n), q(2*n, "0")]
    trans.extend([
        # level 2n
        tr(q(2*n-1, "T"), last_bot[::-1], 2*n, {1}),
        tr(q(2*n-1, "F"), last_bot, 2*n, {1}),
        tr(q(2*n-1, "0"), [q(2*n, "0"), q(2*n, "0")], 2*n, {1}),
        # leafs
        tr(q(2*n), [], "c1", {1}),
        tr(q(2*n, "0"), [], "c0", {1}),
    ])

    return context + "\n".join(trans)


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Generate MCToffoli spec")
    parser.add_argument("n", type=int, help="Number of qubits")
    parser.add_argument("cond",
                        choices=[
                            "pre",
                            "post"
                        ],
                        default="post",
                        help="Pre or post spec")
    parser.add_argument("last",
                        choices=["0", "1"],
                        default="1",
                        help="Last bit is 0 or 1")
    args = parser.parse_args()
    last_is_one = args.last == "1"
    if args.cond == "pre":
        print(gen_toff_prespec(args.n, last_is_one))
    else:
        print(gen_toff_postspec(args.n, last_is_one))
