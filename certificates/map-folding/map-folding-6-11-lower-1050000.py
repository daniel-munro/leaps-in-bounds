"""Print COUNT foldings of the M x N map, one stack per line, from the bottom
up, with the cells numbered 0 to MN - 1 row by row: one base-36 character each
for maps of at most 36 cells, or decimal numbers separated by commas.

Each is a product of foldings of strips of stamps. For a folding s of the strip
of N stamps and t of the strip of M (s[j] and t[i] being the levels of stamps j
and i), giving cell (i, j) the level t[i] N + s[j] for even i and
t[i] N + N - 1 - s[j] for odd i folds every row the same way and then folds the
strip of rows. Swapping the roles of rows and columns gives as many more. The
first half of the stacks printed are of the first kind and the rest of the
second, each for the strip foldings in the order a depth-first search finds
them, so the output is the same every time."""

import sys

M, N, COUNT = 6, 11, 1050000
CELLS = M * N
DIGITS = "0123456789abcdefghijklmnopqrstuvwxyz"


def strip_foldings(n):
    """The foldings of a strip of n stamps, as the list of stamps from the
    bottom up, in the order of a depth-first search that inserts the stamps
    one at a time and keeps the creases on each edge nested or disjoint."""
    if n == 1:
        yield (0,)
        return

    def search(stack, k):
        # The new crease (k - 1, k) is on edge (k - 1) % 2, with the placed
        # creases (c, c + 1), c + 1 < k, with c of the same parity. The new stamp can go in
        # any gap in the same region of their nested intervals as stamp k - 1.
        parity = (k - 1) % 2
        regions = [0]
        opened = []
        current = 0
        seen = set()
        for c in stack:
            # The stamp joined to c by a crease on this edge, if both are placed
            p = c + 1 if c % 2 == parity else c - 1
            if 0 <= p < k:
                if p in seen:
                    opened.pop()
                    current = opened[-1] if opened else 0
                else:
                    seen.add(c)
                    current = c + 1
                    opened.append(current)
            regions.append(current)
        r = regions[stack.index(k - 1)]
        for gap, rg in enumerate(regions):
            if rg == r:
                new = stack[:gap] + (k,) + stack[gap:]
                if k == n - 1:
                    yield new
                else:
                    yield from search(new, k + 1)

    yield from search((0,), 1)


def write(cells_by_level):
    if CELLS <= 36:
        return "".join(DIGITS[c] for c in cells_by_level)
    return ",".join(map(str, cells_by_level))


def products(m, n, transpose):
    """Products of foldings of the strip of m (rows) and of n (the cells of a
    row), for the m x n map, or with transpose for its transpose: then rows
    are columns of the M x N map."""
    # The levels t[i] n to t[i] n + n - 1 hold row i: its cells in the order
    # of s from the bottom up for even i, and reversed for odd i. So the stack
    # is the rows in the order of t, each written out once for each s.
    sep = "" if CELLS <= 36 else ","

    def rows(s):
        return [
            write([j * N + i if transpose else i * N + j for j in (s if i % 2 == 0 else s[::-1])])
            for i in range(m)
        ]

    # Only the first few foldings of the longer strip are needed, so list
    # those of the shorter strip and loop over the longer one's as found.
    if n >= m:
        ts = list(strip_foldings(m))
        for s in strip_foldings(n):
            r = rows(s)
            for t in ts:
                yield sep.join([r[i] for i in t])
    else:
        rs = [rows(s) for s in strip_foldings(n)]
        for t in strip_foldings(m):
            for r in rs:
                yield sep.join([r[i] for i in t])


def main():
    first = COUNT // 2
    out = []
    for kind, total in ((products(M, N, False), first), (products(N, M, True), COUNT - first)):
        printed = 0
        for line in kind:
            if printed == total:
                break
            out.append(line)
            printed += 1
            if len(out) >= 10000:
                sys.stdout.write("\n".join(out) + "\n")
                out.clear()
        if printed != total:
            raise SystemExit(f"only {printed} products of this kind, not {total}")
    sys.stdout.write("\n".join(out) + "\n" if out else "")


main()
