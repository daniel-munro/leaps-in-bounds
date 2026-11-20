"""Print arrangements of 7 lines of pairwise different combinatorial types,
one per row as 21 integers a b c, one triple per line a x + b y = c.

How: start from arrangements of 6 lines of all 791 types (the witness of
affine-line-arrangements-6-lower-791, embedded below), and add a line to each
in every way that gives a different arrangement. A new line y = m x + k
corresponds to the point (m, k) of a dual plane, where the lines through a
vertex (x0, y0) are the dual line k = y0 - m x0, and the lines parallel to a
line of slope s are the dual line m = s. The new line's position relative to
the vertices, and its direction relative to the lines, is the same throughout
each face of the arrangement of these dual lines (each vertex, edge and cell),
and that decides the type of the new arrangement. So taking a point in every
face, except the points that are the lines themselves, gives every type that
extends this realization. (Vertical new lines aren't needed, since a type
with a vertical line also arises with that line slightly turned, or, if it's
parallel to another line, after a shear of the plane.) Then mark another line
as the line at infinity in each arrangement found (see to_infinity): an
arrangement of 7 lines in the plane is one of 8 lines in the projective plane,
with one of them marked as the line at infinity, and lines are parallel when
they meet on it.

Types are told apart by a canonical form that is the same for arrangements of
the same type (see form()), and an arrangement is printed only if its form is
new. The checker decides which arrangements are of different types, with its
own canonical form.

Deterministic: everything is computed with exact rational arithmetic, there
are no random numbers, and nothing depends on the machine or the order of
iteration over a set.
"""

import base64
import lzma
import math
import sys
from fractions import Fraction

BASE6 = (
    '{Wp48S^xk9=GL@E0stWa8~^|S5YJf5;CYi2H(dZ22m+Om?~MZ#KQCe6E$@Cucq#{3lo@>jnvmnV7'
    'a4=aTL?g)KZ<yOJA+7n&)81yXB-~(A-'
    '<5#=2c4)q{zd!pT+a*oAY7rW7vnyp7Oa_VYqd(tLTbL`By~bE57J4qIQy?n!PK|+?=4Ue#OXOsMs'
    '^_F6)bv>A5|u(cNh+JBvnGj7wuvl!A}2c!?O|4QBN{z2COKvt0`>O4K@L<~#;e7#x@`O~_==scDE'
    'IiaJNPi{0d8KkCwUVNCW0?Bld<Lf*%3A@<h5iUy&BhJ6yW8<hr8=oQFKor3lIda6I{9E<M{{L)VD'
    'RUyj+46t?$qAN>2BAoD^n1LBGOD#2!um!GlELrU7=BT4HhqhLAhC-'
    '2|?l9{Bs<P9?uD<H3OU0Xiv^6s0`i~|ip%Z`07G-'
    'WS9xea5&+k45)8~z%Q^nvg{R@_V8qGzr1~KR-6Dg2~#`5POl(Ol?uzot+#Oq660YP0-$-'
    'Q)k)w)h!AeaZv>q!BW6W7N|g=ZjpQjFLLt_#MQD83=zxSHsbNoDwjx%4KMn~nHT%2_2I?GIuo73_'
    'UuTQT|y30Oi>+F1@-'
    '3<(6gR@Rmy&7>X|J_rO;DWex4`oAo`mZSzUsOO#Yvrmu63r36bV)vYp&*nEOKWy~=bomBT)$w$pI'
    'yGt%%evx+4lU=bLPm|21&Pm6+lAiQClv<k=p7x=A&`>#oCkJ00iW_~QYQRywso|Pxa0}UM41wFCf'
    '8Fm(~z3k66~n0gqXRJ`sL7HGWELe(mT$hOIf>rgkPLpY3k@*+q7)rS1>ohvf{9`x0D4Y7Rt(V)~L'
    'mN1sTErp{_P)!YeT+b{iOn#nTf6Nw|svA)~hQ-'
    '_4i$u=9ifRc5wK?YgnhF6v46O9p2ldt@@SWGrpn=1R`!x`D8)mF$doG=!4IS=%uJ4;(BbF)b5gUe'
    'w8l9gD+0r>rWwPWRJPTHAg?nG3(0Yd<0}E;4Z??;m4)6^b65$JQ3f^DqXd^PY&A;8);GDrA@=4Zw'
    '62MQCxZG->(}b>2tYQ6>>_v-sVl=+Eknfn@T(au^WH+g$^G^djg-'
    '?)%UCz`z{LZa(@Pv~8Dnv^x6*20qHNh%fYQZ}xO{FUcX;@+=L|Z?mUU%L^~ZZZE$q$cRUrpm=v&i'
    'll4~!{4?}V?@^R&gDp4ry-eO!cNY}sq>X(b)w<H?@)|kC6fb$U9F@Y#(<KI`~+j^&y3&2Xf~RD{_'
    'p1w)prbcsknYiTfoSYd|dFLJiy7PksK}y{H~kwavHiGxdb!p&EKB!0ERJJ^Ql(JSj=?@LIKd#3fJ'
    '`llq+|^zy`oyPko-U_2~cVSAd50oWUS<XWHVXS87hOsq7-7#j>V#f7hqBQxxD5nMs@YN@&u)KW7-'
    'FsNB4XDy1;pQDT=%uv3=T7*&{(58=B%ip0lI(2irvGenHzsTlOwXsC(Uk|g|^sWR$QYfnH%bNmBq'
    'ZZEZel56#huz<~$AfDnZPnx&*JnrRTl!DCri`$YK!e9}>;jjg3OT|95E}Deo-ICLnvr3^r-'
    '%>2`fKsD<z6|sW5Ei^W2?9XNJdLP~pC~tY=AZGC+Jw+Ca=<5=ofE>awV(5GPLRgAk;ipMVU1Q~=g'
    '+5my6pr`M@HQ#_43n(mNTRUDr%3V^38Qphh}f6RK&@E3O0QW`F%7n(YijUUn5g?4HW4n2{cg^3Cv'
    'SufB=(U>f7f@20__s_~3M#z-'
    '*mAW(An|W{hxEqGnUfm4%JZ$ti~Kxs+h`whxY+<!_VZX{Uk~i9?@7PR;wc4E^JpIib8M_Jn`TWEZ'
    '^?FAi8>0!VwSDj?lxy?esKm{8_vQzv;iQH=EI<nSf@uZ+?lcC@04eY6(~`+ou5gZW_UoER>C{)f`'
    'N<(aj}lG99K=KV;8vA3MwMm)shn!(%wIQ-v8hmx5D_#J?vqS=COG}5)Y`a&d0a-+t@7Msk-'
    'o7#H+#g}sBziVf5A{cU9bbUvkvU(oS7QY=w#jJ`tjxpYrbRxRR1hkr2C7mo%9EK<c?e$C`6ReI>w'
    'L8icApIz{clx{$O>Wc`#}t*bY5xmUwNQLHUN^5P9gsdz!69e%AG~YC{Rdk$<;_dFKKx^VeC*-'
    'KW}wVhwaaS5mx#mk^7gQC-'
    '2+Pq^ftN_63IY1C1b9H{J1&f<nxu*p!><Vx`q#G_^iEc1Shk*C@WJM5yOex_)EYvymxA$`ujS4dp'
    '(3)d%&?QKi)n#ZG*vOw$~<MovEe$MS(;WXc)6_;g)J2r}xGYBYny*0sD3xkxl}K5!B%3k>#MJntD'
    '(W1;iGdh_cyUdO=fyjhS=osFLdE$Y?}qnh@7<URY7jvhU-'
    'L2F?4Th>VWQP&f>t?QvRFhhe(nkA<L4eZx33Rz5AZF?5$qK$r|?0?G=LZph$7>;v7jyi^n5L>cOR'
    '<70@K$JE+=qX`Sdt0LO8BE9|m-(!=GQ#KgH*ohzf;r~RMr$x<I-}e;HXJ}2HZbV`#T-'
    'Tp5`F}<C%H(f`X(pRfRBCetuVh{)Pb+RJf=<l#ifVURc_PgzR?3C6ANr#667K$ruVaU@(Qf+NzJX'
    '1WQNq+MuCMPXv-&#Bx|_*lh0253(HDZCPz#5<G(vx<irD-0uBil>+lPCMZH8a8I&*}>;T6D-'
    '3b6sTa{d!RjzLS#ye4TDgqk5<&s9K8*MORkK{sx(!3XMwaUuBe{IuM>G#}K-'
    'dWUl7P<^>*=<w8>e5x{o7>ja#3v&}g?ik=xWS8$)_TAK2hHvG^0igBlwW-'
    '3C6Gd&6JoTRE*WIAEqusGT2nOMR3|OotBc-M(Ph1SIjE`uRAeUW%071-'
    'u(ieP3=OI&{1E1I|19=LFgYi;XPh)I~ftA(ld(LFIdI+PBk<4=JE9q)K?}!_rbK+FR{$EgvDwfQ4'
    'SOOQqGE+}kU*7A$tUA-'
    'M!K=}4X($)&BTRma9gvkX`40aQuiD#p*ZHg`9G^oDdgfS2w*K;cnInTKT8otG+8o0(#BA1S&rJ*K'
    'DB!=#=1LtXMDn^nWjQD(ErSD`IqX%~S12P6Y&O9EGjuiOSa&&|b)VgO5ua8V94jH%Y#9ePXD^Igy'
    ')e7dMLGlK17S~|_U&i_Xc|Yl30;E<ybH0DtbT8$Sn-'
    'zCeUo!F9p?g9uj3-sxd}93+|VnscUWg5X@O&*0=%0`nJKjx-h6L7t_G-ULI)xR)RXFVN0BLVQ1(3'
    'TqHr#0$O`Bxz*7sH@Gtl)L3GjMgxTM7k~m(t4Fcppq%-'
    '*R$0zwq^Z#BTt5o|qiP|_(Iq+^!=?CX^YGY{pZ)0|Aw+zqi6viM!I3u>)3SQPhX(s4(R>WCbrGlo'
    '>^o^B3va<}+seAlncX)Q;iMz9u0_Z(LzBB9Yg9DO5%wriYuMdP>h1D1uT(vEDa<YvKhJM@$w!<Mt'
    'x<V&r^pPb5Gc1!cYn&5K&%Pr<a^k-'
    'cKV9~)bOq4A@*1jss=jLk=y!(=oy#LyW4ifgGmbE>pLUg2PJc&yQv$pn0h}skf%lA?>)nz8JIi{z'
    'S}q(WJw-b7cn%Xb`a6bOu1v`H4V?%FgSX-b-mo1glJ6Xa?1EQ0s#>S=ItIStabnAhT>xpX&O@otL'
    '0UYQ9<jTHW5V9<N_jzVo9*?Fz;v_Tf=xHB;1SbM)+jATM*;!O5~m@c)-;b@f7D~Cs-'
    '5V@ix8G$1_Z8wG}?Vq<>b2<?tgyf;T;?h#+IilL7M<?MVf>3zvHMYww94jsnomKo1*<my}59$IWX'
    'F>`sXd}O`LV7qVTPo;z)H!?Nxj_TnId1grfT_TIqTF!IS>dPzr|Wsgjj`f^kvuzM+GR8An`d7Ywb'
    'WO~-6WX=Su9WVb$HZu^hQq&k0wiD-FT81Q3N_kruzteLk^k%0^B%V1}HxgbrIB2!^aS+#bj(gDkX'
    'q<jWhp*8FKQlT&4oFLSqLA+(74{bIUPK~5rkYd_i8$^&1>&9pTIAUPaHtl*0uAIX-'
    'Ds9W?dKR|km~_lu5CV?qhtK*^-~6vm>`Zl62ilL-FgfJK%Eu}#xTL7*n>J4@X7$COo-zAYEq94n+'
    'DguDd?Prxp^3L-'
    '%+Oa%;!+^U!B4FA3Qq3+zh6}`+LR9^u~l89TC9kI*8YD#7#9Bip4;s!n~|G42~rpzQd{JhFxhe)-'
    'pNF`2-Ceu-P|jVwM-'
    '*5k>vD4z*3@EF;c0uT<w_y?G`$QKquAvZWb6J>dSW#24()EAX#J3wl9Dil?H>wthm@+V%)cjmy)3'
    '#hImT`dxIpJLSD+s+7C9n08rmH%BxGKNsV%MkmT$gTZd-'
    't7%eaCs|0Jfap=bfdbAwC@{UZ@L)PZmIj+a?Jnh!Yzfcd~Ce6St{5kiZ@EM|_`JW+|f<5`;ml^p?'
    'DMixqmB=!)XY5T%EB#>=Vc*eGgxG}iuR2ayruRl6*z_B|E>f8UNa7$`8I<xKo%=SO<xz^><Z5w`0'
    'pQ=BXeyM*oLp9&j|kYv;u)BX4<{uxo1&bQcJ3uzKmM2(vVgJOwlFq7w&9?}9wf!D1<SS1O^Ky#mX'
    '{Tljbh9?tJcW?2#;v8Vo*<4n#@Ts$(S0*FC@Ekt<tG<hiU{I{yHP<#=|swp51^vl)~!m@&AtBHm6'
    'oI4?DASeCs6r9<o(QBIv)9tS!c}5lMNq4es^se6RDQ-'
    'H}bN&baYoyGbtwOaIwB6W7pouS#)i667W+?;KhUI`wZ5bY0isQBf@MURKQFG@Y-'
    '9kAIcH70A_MS~SNIgO)=B!H%y7JXrDgG&ZP-'
    '#pAyNEdpH>T}8tO`$ZpMQc`lwwHu~tKdW?{^pSR6;Dj)2o>+-'
    '4zM63JXhWgsfGoR;>f>hbRDB*Q2vgR1{?`CZ>XA^cRY;JRCtOq?pke;fo(x`Ra25(|FU1ia-AlVr'
    '=lx)rB-2>^dzo{ewLgT-%rX57B-'
    'c9yoM&|^3<PpiJFdR{A50o8J}`@Z%V^<DJdx=Gb?}BSWEL!@SbKQ_9DD;(;DCu7i3qejpHcZM+)2'
    'n=LYM4Od|a2${l9f!!coE8{W2sf>E68JdESI69Cdg7;t?U!zlnPO{u8M5F2r%jmE6jPFeR0R^o=&'
    'ri^_0zKD(n-'
    'N|63O$g*N4%gEY1_$Ik^Yx78Wyyn8|%FNdRUT)dNyHF&a%z&zzI#V6tS2QbR>87~8RCm(Armle*='
    'tXjs(>hQaGyrm-(mYN8Na;@Mj~O!_-<5SQ-'
    'g!;s`5EaEVFxCHQtX`BCggY&Pj44486+FHw}U4nZDJ_w5~nMtH7O8XM#4YOkI#~^b;;q&(8qxpY!'
    'Dftii$8)W|V{JShO+^Z(TwV+!D<*Z_T44_kG5EVVwLfVKNpr7!X4>{Hl%C2a{)7{3@3%sH5r<H*?'
    '=@+#=UpgxmXhW5-Zk8`fo81C~6T0x|KA5IDXgbt9Ene{95dpEdy-'
    ')+vi$eUf*AfEVBzVWYQ^mG8^Z6q8%n0n>7Le<e&9L5%yxnVZ(}!zo;4Mm^jlG65b%dxyi{JCRV%n'
    '%D;EAzwp|=YkJa4+s3xo0skyKyx7CS;U{4AGnc%k&wU7%j&1np{s-'
    'z*H`NobsMooWCx%^DLz530kapwnLPDsP_~JLT9nj|Znyuo7Dh%@=?fd%MFPKL=yn0S=5j~lqzFdK'
    'u}Jj9X4CXN<}>;x+b;7&khnwMTv=x`B@!013xi|3X}z!dcP?>1sm}j=5YB%-o91rbyh>-'
    'kiQKdDm)IJT#Nem!z7wS4BbOvx_fk_zesUV+%p1cD;5RQ%?U%rs79<-'
    '}m+&v&FWC|M8)8y*a*UOkjdquR8C=t#n><?f&F_-CA<9$X;$C%|g93Y*!%sxU=ou#C=bz`y7(R!D'
    'u5LN_jGD?Ht1xQFy29l+gMc&&5TMp+cqa!w;sQqK%hor6lAn(#Pajl7CxbcVP4Xkonf<~qcr;BwZ'
    '#uiEoWd&1wF(|Kac#{=7Pv)Y48=XKc)mAAmLxdmI7qJdX9S4pYU8Iq=R|-'
    'U&URq@acHz1<n;?<&a#@3;tH~wL{-$1D-'
    'tlk(*FnjElHu2ChRbNuWNy<S~f+W#e^n(7f@MeG|oLoO`W4O@jWb8JgM90yOeLiqWZ2~s8uug<Gl'
    'E<&u{4Y1xrPkkKia!j{Ya7RbivLSY9XovNMB9a>`Ba(5cst_-x6st()6R;hLHHxDQ2)wR0^EdxL-'
    'IPd}Tc{tOxzO-B64U#bFZR~sesTnUeBLB6%#J$N3~@ma!JeegSW&zrM&P4SIW+Hdk3@j-'
    'P^hlbS*e)6_8Ry!g+gxJ1BB-+P;nSs(hyThMGG7x$F2HF%9z8&`0EN`jRPgm#R-'
    'cl%>#3sF45pB1z82n;6`s+Eg{5ozz|B08!$z-'
    '62uvhLSA8ABk!PkhD8kz($Qt~Q&Bfzg;GFjFFogXA7V`@bJ_X(F(huP4VDPg;Zii@^6iPd!)RU`b'
    '(aEMX(gv9|z{r^@@(n$o1Q2T|#`8N3;;zzcv5K7vUPK}c--'
    'C)SQaU>4=K^6O@nu(&2%!$Ul__19zG2sJvV^M+%arD4`6N{)$7bT=vKs-'
    'ke&Zhu4MG;jNjppK=rSeM3Zp;5rTcO-yOU@vO<m+GjfQNGzGIA}Ovq=#HYtaL5+7G>g{*U)%SItS'
    'Wtu9!Rcjtp!JMpW5n;5TCv(4+#T&fTj|2?)Z^$mb`vi5qi8WR~=XNM+lXmhpoW$fFYogJfeLXhVE'
    'uK<x-0exNmqnzouj9z`M!-'
    '7=rC2PI8S3>Bk6ixoewu<G^UEt%X^62#bSpWb4uIQjP%^6V^00Gk|l=A@qqEz)dvBYQl0ssI200d'
    'cD'
)


def norm(a, b, c):
    g = math.gcd(math.gcd(a, b), c)
    a, b, c = a // g, b // g, c // g
    if a < 0 or (a == 0 and b < 0):
        a, b, c = -a, -b, -c
    return (a, b, c)


def vertices(lines, i):
    """The vertices on line i, in order toward its end in direction (-b, a),
    each as the list of the other lines through it; or None if two lines are
    the same."""
    a1, b1, c1 = lines[i]
    crossings = []
    for j, (a2, b2, c2) in enumerate(lines):
        if j == i:
            continue
        det = a1 * b2 - a2 * b1
        if det == 0:
            if a1 * c2 == a2 * c1 and b1 * c2 == b2 * c1:
                return None
            continue
        x, y = c1 * b2 - c2 * b1, a1 * c2 - a2 * c1
        crossings.append((Fraction(a1 * y - b1 * x, det), j))
    crossings.sort()
    groups = []
    last = None
    for position, j in crossings:
        if position == last:
            groups[-1].append(j)
        else:
            groups.append([j])
            last = position
    return groups


def ends(lines):
    """The ends of the lines in counterclockwise order around a large circle,
    as in line_ends in scripts/certificates/families/line_arrangement.py."""
    def key(end):
        i, (x, y) = end
        a, b, c = lines[i]
        g = math.gcd(x, y)
        x, y = x // g, y // g
        half = 0 if y > 0 or (y == 0 and x > 0) else 1
        angle = (0, 0) if y == 0 else (1, Fraction(-x, y))
        offset = Fraction(c * (-a * y + b * x), a * a + b * b)
        return half, angle, offset
    result = [(i, u) for i, (a, b, _) in enumerate(lines) for u in ((-b, a), (b, -a))]
    result.sort(key=key)
    return result


def form(lines):
    """A canonical form of the type of an arrangement, or None if two of its
    lines are the same. Walk around the ends of the lines, numbering the lines
    in the order the walk first meets them. For each line in that order, list
    its vertices in order from the end the walk met first, each as the numbers
    of the other lines through it. The form is the smallest such list over the
    start and direction of the walk. An equivalence of arrangements takes the
    ends in order around a large circle to the ends in the same or the opposite
    order, the lines through each vertex to the lines through its image, and
    the order of the vertices along each line to the order along its image, so
    arrangements of the same type get the same form."""
    n = len(lines)
    from_end = {}
    for i, (a, b, _) in enumerate(lines):
        vs = vertices(lines, i)
        if vs is None:
            return None
        from_end[(i, (b, -a))] = vs
        from_end[(i, (-b, a))] = vs[::-1]
    order = ends(lines)
    best = None
    for start in range(2 * n):
        for step in (1, -1):
            number = [-1] * n
            first = []
            for t in range(2 * n):
                end = order[(start + step * t) % (2 * n)]
                if number[end[0]] < 0:
                    number[end[0]] = len(first)
                    first.append(end)
            f = tuple(tuple(tuple(sorted(number[j] for j in v)) for v in from_end[end]) for end in first)
            if best is None or f < best:
                best = f
    return best


def no_vertical(lines):
    """The image of the arrangement under a shear (x, y) -> (x + s y, y), of
    the same type, with no vertical line."""
    s = 0
    while any(b - a * s == 0 for a, b, _ in lines):
        s += 1
    return [norm(a, b - a * s, c) for a, b, c in lines]


def face_lines(lines):
    """New lines y = m x + k, at least one for each face of the dual
    arrangement of `lines` (which has no vertical line), other than the lines
    themselves: each vertex of the dual arrangement, a point inside each of its
    edges, and points on either side of each of those, closer to it than to any
    other dual line."""
    points = set()
    for i in range(len(lines)):
        for j in range(i + 1, len(lines)):
            a1, b1, c1 = lines[i]
            a2, b2, c2 = lines[j]
            det = a1 * b2 - a2 * b1
            if det:
                points.add((Fraction(c1 * b2 - c2 * b1, det), Fraction(a1 * c2 - a2 * c1, det)))
    dual = [(x0, Fraction(1), y0) for x0, y0 in sorted(points)]  # p m + q k = r
    slopes = sorted(set(Fraction(-a, b) for a, b, _ in lines))
    dual += [(Fraction(1), Fraction(0), s) for s in slopes]
    count = len(dual)
    on = [[] for _ in range(count)]
    for i in range(count):
        p1, q1, r1 = dual[i]
        for j in range(i + 1, count):
            p2, q2, r2 = dual[j]
            det = p1 * q2 - p2 * q1
            if det:
                point = ((r1 * q2 - r2 * q1) / det, (p1 * r2 - p2 * r1) / det)
                on[i].append(point)
                on[j].append(point)
    # The lines themselves are points on the dual lines of their slopes
    itself = set()
    for a, b, c in lines:
        point = (Fraction(-a, b), Fraction(c, b))
        itself.add(point)
        on[len(points) + slopes.index(point[0])].append(point)
    result = []
    seen = set()

    def add(point):
        if point not in itself and point not in seen:
            seen.add(point)
            m, k = point
            d = math.lcm(m.denominator, k.denominator)
            result.append(norm(-m.numerator * (d // m.denominator), d, k.numerator * (d // k.denominator)))

    for i in range(count):
        p, q, r = dual[i]
        crossings = sorted(set(on[i]), key=lambda P: -q * P[0] + p * P[1])
        for point in crossings:
            add(point)
        if crossings:
            edges = [(crossings[0][0] + q, crossings[0][1] - p), (crossings[-1][0] - q, crossings[-1][1] + p)]
            edges += [((P[0] + R[0]) / 2, (P[1] + R[1]) / 2) for P, R in zip(crossings, crossings[1:])]
        else:
            edges = [(r / p, Fraction(0)) if p else (Fraction(0), r / q)]
        for em, ek in edges:
            add((em, ek))
            nearest = None
            for j in range(count):
                if j != i:
                    p2, q2, r2 = dual[j]
                    den = p2 * p + q2 * q
                    if den:
                        t = abs((r2 - p2 * em - q2 * ek) / den)
                        if nearest is None or t < nearest:
                            nearest = t
            e = Fraction(1)
            while nearest is not None and e * 2 >= nearest:
                e /= 2
            for s in (e, -e):
                add((em + s * p, ek + s * q))
    return result


def to_infinity(lines, i):
    """The image of the arrangement under a projective map taking line i to
    the line at infinity, and the line at infinity to an ordinary line, which
    replaces line i."""
    a, b, c = lines[i]
    # New coordinates (x', y', z') = M (x, y, z), where line i is
    # a x + b y - c z = 0, and line l (as a row vector) becomes l adj(M)
    rows = [(1, 0, 0), (0, 1, 0)] if c else [(1, 0, 0), (0, 0, 1)] if b else [(0, 1, 0), (0, 0, 1)]
    m = rows + [(a, b, -c)]
    adj = [[m[(s + 1) % 3][(r + 1) % 3] * m[(s + 2) % 3][(r + 2) % 3]
            - m[(s + 1) % 3][(r + 2) % 3] * m[(s + 2) % 3][(r + 1) % 3]
            for s in range(3)] for r in range(3)]
    result = []
    for line in [line for j, line in enumerate(lines) if j != i] + [None]:
        l = (0, 0, 1) if line is None else (line[0], line[1], -line[2])
        p, q, r = (sum(l[k] * adj[k][s] for k in range(3)) for s in range(3))
        result.append(norm(p, q, -r))
    return result


def extend(lines, found, forms):
    lines = no_vertical(lines)
    for line in face_lines(lines):
        new = lines + [line]
        f = form(new)
        if f is not None and f not in found:
            found[f] = new
            forms.append(f)


def main():
    rows = lzma.decompress(base64.b85decode("".join(BASE6))).decode().split("\n")
    base = [[tuple(v[3 * i:3 * i + 3]) for i in range(6)]
            for v in ([int(x) for x in row.split()] for row in rows) if v]
    found = {}
    forms = []
    for lines in base:
        extend(lines, found, forms)
    k = 0
    while k < len(forms):
        lines = found[forms[k]]
        for i in range(len(lines)):
            new = to_infinity(lines, i)
            f = form(new)
            if f not in found:
                found[f] = new
                forms.append(f)
        k += 1
    for f in forms:
        sys.stdout.write(" ".join(str(x) for line in found[f] for x in line) + "\n")


main()
