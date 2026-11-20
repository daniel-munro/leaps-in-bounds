"""Print every folding of an M x N map (a strip of N stamps when M = 1), one
stack per line, from the bottom up, with the cells numbered 0 to MN - 1 row by
row, one base-36 character each.

The search inserts the cells into the stack one at a time, in row-major order.
Inserting a cell adds the creases to its left and upper neighbours, and the
relative order of the cells already placed never changes afterwards, so a
crossing between two placed creases can never be undone: the search abandons a
partial stack as soon as one appears, and every folding is reached exactly once
(by the order its cells appear in, cell by cell).

A new crease from a placed cell c to the new cell k, on one edge of the stack,
crosses no crease already on that edge exactly when c and the gap where k goes
lie in the same region of the nested intervals of that edge's creases. One
scan of the stack per edge finds the region of every gap."""

import sys

M, N = 3, 6
CELLS = M * N
DIGITS = "0123456789abcdefghijklmnopqrstuvwxyz"
CH = DIGITS[:CELLS]
INDEX = {c: i for i, c in enumerate(CH)}

# partner[g][c]: the cell joined to cell c by a crease on edge g, or -1.
# Edges: 0, 1 for creases between rows i, i + 1 with i even, odd; 2, 3 for
# creases between columns j, j + 1 with j even, odd.
partner = [[-1] * CELLS for _ in range(4)]
for i in range(M):
    for j in range(N):
        c = i * N + j
        if i + 1 < M:
            partner[i % 2][c], partner[i % 2][c + N] = c + N, c
        if j + 1 < N:
            partner[2 + j % 2][c], partner[2 + j % 2][c + 1] = c + 1, c

out = []
size = 0


def gap_regions(stack, part, k):
    """The region of each gap of the stack (gap g is just below the g-th cell
    from the bottom), among the nested intervals of the creases on one edge
    between cells below k. Regions are numbered by the crease that opens them,
    0 for the outside."""
    regions = [0]
    opened = []
    current = 0
    seen = set()
    for ch in stack:
        c = INDEX[ch]
        p = part[c]
        if 0 <= p < k:
            if p in seen:
                opened.pop()
                current = opened[-1] if opened else 0
            else:
                seen.add(c)
                current = c + 1
                opened.append(current)
        regions.append(current)
    return regions


def search(stack, k):
    """Extend a partial stack of cells 0 to k - 1 by inserting cell k."""
    global size
    i, j = divmod(k, N)
    allowed = None
    for g, c in ((2 + (j - 1) % 2, k - 1) if j > 0 else (None, None), (((i - 1) % 2, k - N) if i > 0 else (None, None))):
        if g is None:
            continue
        regions = gap_regions(stack, partner[g], k)
        r = regions[stack.index(CH[c])]
        gaps = {gap for gap, rg in enumerate(regions) if rg == r}
        allowed = gaps if allowed is None else allowed & gaps
    ch = CH[k]
    if k == CELLS - 1:
        for gap in sorted(allowed):
            out.append(stack[:gap] + ch + stack[gap:])
        if len(out) >= 100000:
            sys.stdout.write("\n".join(out) + "\n")
            out.clear()
        return
    for gap in sorted(allowed):
        search(stack[:gap] + ch + stack[gap:], k + 1)


if CELLS == 1:
    print("0")
else:
    search("0", 1)
    if out:
        sys.stdout.write("\n".join(out) + "\n")
