"""Print an R-coloring of the integers 0 to (K - 1) P with no monochromatic
arithmetic progression of length K, so W(R, K) >= (K - 1) P + 2.

Rabung's construction: P is a prime with P = 1 mod R, and G is a primitive
root mod P. An integer x that isn't a multiple of P gets the color
log_G(x mod P) mod R. The multiples 0, P, ..., (K - 1) P of P get the colors
0, 1, 2, ... (mod R), which aren't all the same.

A progression whose difference d isn't a multiple of P has residues mod P
y d, (y + 1) d, ..., (y + K - 1) d for some y, and multiplying by d adds
log_G(d) to every color, so it's monochromatic only if the residues y to
y + K - 1 are, apart from 0. For this P, no K cyclically consecutive residues
have their nonzero members all the same color. A progression whose difference
is a multiple of P fits in 0 to (K - 1) P only if it is 0, P, ..., (K - 1) P.

Prints the colors as digits, 100 per line.
"""

import sys

R, K, P, G = 4, 11, 299993, 5

# The color of each residue mod P, from the powers of G
color = [0] * P
x = 1
for i in range(P - 1):
    if i > 0 and x == 1:
        raise SystemExit("G isn't a primitive root mod P")
    color[x] = i % R
    x = x * G % P
period = "".join(str(c) for c in color)

colors = "".join(str(q % R) + period[1:] for q in range(K - 1)) + str((K - 1) % R)
assert len(colors) == (K - 1) * P + 1
out = sys.stdout
for i in range(0, len(colors), 100):
    out.write(colors[i:i + 100] + "\n")
