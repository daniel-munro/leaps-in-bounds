"""Print arrangements of N lines in general position, one per row as 3N
integers a b c, one triple per line a x + b y = c.

How: start from arrangements of 7 lines of all 922 types in general position
(the witness of affine-line-arrangements-general-position-7-lower-922,
embedded below), and add a line to each in every way that gives a different
arrangement: the lines y = m x + k that miss every vertex and are parallel to
none of the lines correspond to the points (m, k) off the dual lines
k = y0 - m x0 of the vertices (x0, y0) and m = slope of each line, and lines in
the same cell of that dual arrangement give arrangements of the same type. So
taking one point in each cell gives every type that extends this realization.
This finds 38551 of the 38609 types of 8 lines. The rest come from marking a
different line as the line at infinity (see to_infinity): an arrangement of 8
lines in general position is one of 9 lines in the projective plane, no three
through a point, with one of them marked. Each arrangement of 8 lines found is
replaced by one with small coefficients of the same type, by rounding.

Types are told apart by a canonical form: for 8 lines, general_arrangement_type
from scripts/certificates/families/line_arrangement.py, copied below; for 9,
the same form computed with floating point (see batch_forms), which is only
used to skip repeats: the checker decides which arrangements are of different
types.

Deterministic: there are no random numbers, and nothing depends on the
machine or the order of iteration over a set. Exact rational arithmetic decides
everything except which candidate lines are tried for 9 lines.
"""

import base64
import lzma
import math
import sys
from fractions import Fraction

import numpy as np

N = 8

BASE7 = (
    '{Wp48S^xk9=GL@E0stWa8~^|S5YJf5;O-'
    'YP09^nZ2m)kE2dpcg;Rl$GzUHub$*LCfy@UYF#0IX=D;zzNI|m<O=_^n1kL2kev=;o>XM>B01Fg2'
    'W;6MZ|0oM)Bal#GRmRr*4Ek=vsBz1F)Qnj2i^&IO0eE0<>ZiJX%njTd~K%f5{{Jb{mcV{Pa$THKI'
    'Ffke1yE;4T_0gPq;z`Dw1;CoFh6PZPQ$H1iUo2gF>B)Mu%lLCeKe8g)hyeS3p=B&gA|pXuC@kUQI'
    'uZ}m^Jw`s<fv;?6Owk_^K$*Gr(0allG20e_A^L67CxIT0jO=e4TGgYhD)Ukw+~fzIzpMPDXij<1B'
    '<5Rc&dkW$UJP24nD(`hS+W85dH~JGoAW&9qLYZ%Rh0X2znp^(I#);WmM0=HK#%^&`_YsGwWe^LJO'
    'b4P(siuu1BK@Cj<BWX)tqW?apfG8J%a!D#UdBR_0I+hsCOn6)8){&5hApZ&UMx15xG$A5=|g<u23'
    'c9uMbH$?Puvd`@*s$3C%r!Q}A9pOaB|HcTUW-'
    'I?1QMs2_18QdBARtwB}%fU%?9q1Pc)Lc_>;ztWj@~vbsr${7DlHEw)0&ft5e7S@wJ&?$iD(qw3MA'
    'utw!e`*{BzDIE3TxiRsk0Mq-'
    '|Kq2v{+NMTi358Bsn@OA)ec3cf0{MNPG5o)rAQq{Mt}pWT$62R7e)UjRc}=-%2VW7mUjyDn-'
    'dr?(Gc=L>fw3vwMuB*```|#*uliku#c!(Q&FW9>Fbr3($Q%8};c_-E_jQc#FU|R7^h(co<2E4cl9'
    'S9OdcGN40KJ@@NtEf^XWpYh`kfUCB$jp%4puo*ZK>58IQ_3QqBPjOq=SZ8m%5lCzIv=AH!^<6q?7'
    '?&j~u_f&zqR{7fX;!krq2M-L+!f{sZ=c5g%##o;-26Q*Y@ll+0?m-P$eV~e-!@c$@`4F~yrY-OWe'
    '^f__vX}lRTN(pO!*J-'
    'iTPY0PfEfqR0ezZ=NZHrKjVO{iGD;Ll$SE*hTpk4RyWQY40Ayw#g5|k?$wV`WlKP_JYAqIXJ-'
    'i9FVkx=XGBofyjcU{)`B1Hb@Iv-nmmBu-_cQd=N%)(lg};_IOSG}@KO7cc1zaAU8aBEdgt%3$DC6'
    'vmT#6sVUZ_AJ$4)T;I?;27(F>86|4De|fc$Q%<WuNpb$TQMX4vE=tC)`FT|u=FQrgInqvDpH-WG;'
    '1F<g9;tzBF0wO`g`ZvgK0t7d&EQ_Hw_S{nQd3`}^PY4AIU7oeEW7l)+RI1r%dDGqwU<6oprS3QMa'
    'lW;SrM+y*Lq<@2}W`LGRnoW%`PqIl+1B}C_8I4e1et8R=yTy`_4fi7NXD+>5iFuL|xx`nLQzF2=a'
    '0AwJW+s5#yTd!aXah`Q`%aqm^@(=wYFbv#j;cT7miC2%p_>ijea5se1T{rJ16V!TCqK$uR?qtOf%'
    'zTkOTD#JAKzyqdMrV!w;UC4+gLEzz>Wzz7LUT3ilVM%J30>|_S<lWX;wZl@=1#Vu}ld5)jB)ghgb'
    'Rv#%&cO0zrmngU+d_fkKqIN1a`FkBf&ae_dCLJW##ID^^@i^mcI;SQxO3B&6lJkO>^=qpTu{407W'
    'sGE$FdgP*i1y`C1{ZnI)lSP^E##DxJKWtB;Piwc`Ts&a+;G6nhbQ|Ilwq7)GA$&%~L#MW}=38{&~'
    'C{YV=D$p4}cD|yJ@weV2*06ql{PgdIHp0(}xD`7Vo*0^B8{d3Mxh?0Ssyi<3N#2t7#el)u?lcukv'
    ';qKl4{^SEALMe<3OAl20qND^(vpSfq97gjE3CezV}c;hG%k$D?#)b@5^Yi%l;p0394cP~8j;f2`l'
    'V^2KV#r+d0f3YiA-2?4!i(-'
    'A@ESqf|D6%56d8N5duxS_L1~xLLp9|;p&bF>lV?ZnP^NYxL{}6K5LG}$AXjQ+c!(;m$l4m9Oc1(w'
    'qFIB6P$kfJYQl#;oSO-eUJP<XH0>_gz(%)oU<!9MIxw)MayAgb;SKd6FkPg?nT4dP|s^Pp{xT?YW'
    'UF8spqrw$ZV3}wK9#r@G!->f&BRZTW)p&8B26BMJ`hX#Z=0-'
    '{>|Hu+f9+fyuDlzmW1;&jgr4L(|~~l>X2g%(4HhhvHdP6>vBd|-'
    'Ci2;MMS+n=JX;;>7edWo<Ts#k{Jx5dCLx?i*}4<n+c3h9Y36bdlOpljyE2`tcgn`WE}6@&72-'
    '@haTOF(y(mpnBDz#0W+DWr5rsFglOd5MW{`oN?PSmZYp07{xk)3gWC*~NPHe$iA5A*dE}GwGOdao'
    'X~Z%mC0g|h5*o)JbYy0hlE-$Wo8Fj8bkl63cEB;?OYLY@g<Sp9*N9UByo#h{1XwP4p-'
    'JiCuNey!{cfzNr8{SG;FavWD#8S0)D|5x`U9!MOkrCcdHNd2GPdVO(+g0@yvcAzMX_^7g)a@P;8D'
    '(Z>+t8AEWlCNNWfU)zpLI?^<MVt82;<Ku?m^jGRIz!4mbEJi(r}LAq;b5D7l1C%MbAJ<Vg~6`z<o'
    'V#QYyGZ69g=*9i&@PIdiq?Zkwd9=Z0$2|SKaJf}w{zCWC)*d|xcz`Ci>7%&>&K!?8E1`^}AMvox;'
    'M}Q^n)q3+hmHV^=hqGo+Ag57QV%W^Cco0RX&M{{PyJ>Lv1Ol-'
    '1l|W7M&NjS0z@a6rhL{6Esde+nHH~|SH4(KNY|MgC90HE1>6D-'
    'iKF3And7J<1hM9Lcnroy2tnMk&ouHk7B9ptAxw=)8%<%}`s+A14vNP3j9=$K-'
    'V*Bj@?){dbG5cVi#V#YE13l0EUJ&ktU&HJu3}$^Ry?oVzD&D)kXu8xNn`|I>acL)GF%keps+ddS$'
    'U^8xR&PL<(Tai7XmqjGUMJsA6OR&msO|R{AHaZitH|15Ucl3zEywHH!5*dApKf0VQO~*Qh|E<Lhk'
    '96qKF$@H&2~91%fGz>tAPO^(EBTswf+JKk~q6$j$ki*GBVJ%7$;Zj@EScQ<J-'
    'D}zm$LkN+3m@Ug0==`z;Uw;GnYuJQ6}SY6FaanTi5+m2OQ6z>Zfj!{Hg9XnVBMOaF+LfKdkTzvG7'
    '&?0Z`5ei>1%M}@j#&0lHqHGq^lEarJ<a5b&!(rj<l$?`sX?lt00Y1-'
    'YxPJ@t>gZ7%;)ek#qEZW?b-'
    'fSqdA#(S}9ScvM&CgMvp=LkVO7Q8cQ~TT+wtQXaQp8|pOJUfd&x5HM*Dr}%IleVrPH3S1)=-'
    '8F$$hn3nRQBGhjdIchL1bTgDYwPcVG~D#aM_`@*}(k9VDs{4d^0Z_{qDdyfx9gG2rh0tQ-'
    '50h+c+bLpRSGzH?{~*gOQf{^8Ke?#3MZud{x1!nY=@wBm^mhQLE>8Ww`}j@f%Plr_424rD`##-'
    '3_}6k%tZMy9MRRtCcOz)>?vs02-U8k7gBcm$uLkAjyj9-'
    'Umy;oOjZPq_US{B^aD&pgUOgbB*wm0rB4p#!o(@OFO;xJx=6Woemikq>D%;D6!?k!m#;tI7=a$s='
    '0Q`OLU*klg;t$+HnM(-'
    'RsZDZ@y!N29}|C8AQgw&?&IevQ~dhJg=~^vm{<+WA1r`}z%>e>O3=8W@}9D(>ClOvyS&@obN~I!-'
    '_O!?@(0s`DGey$hQc3xg{%=Kf3GvILe*`&Z*H?I2#~!)sNXT!Mg<nS*}Mh())EjuZV*fQx+7xjdC'
    'i`|7QkHE>|km;z23Xy}^N<aQxIlyXfH&6MS35uC1^jxIwJQ{0VCr997|h<SeDVW*tA5(>xDhR)_?'
    '!Y-K^IW_$IGt{Gros+A}zFoo--ISdSP0A}7CT1uG#vjYoeb~QQc)tgxXxO5TsdU}h1_|&9@&UH*9'
    'ecB)G}V;z;OV<ZZJpp20ulY^2#jOQFW54k0+dlL`c9u@)C2zAdN0Ywi6`yg&u4W9mSif~^BSJBYr'
    'R|%qod1@6#^YG&TWy$A9WFQNUp#kjjVO!m26UcN?}HRqdPIEub-'
    't%8yvZgg({&Ly`j4OXocrAxn6}>-KLvtEVZBS@~Qja5eQZNH$?zt_p}reBcYzuKMRkav3-'
    'wv*HSTA%zm&F@AJdB*~VyWPIu%9&0nCo@@rSP&QBy<v3%+Ol9fm>cxoRS?_5=i{dy$k9Zj65GH$x'
    '26)N8Mk`^Wrp(M`G04PgW7zMC6@z*$SHkg~6x|^fn5vPGx|0FKkj$9nBZrN!#BE|Z=>2bKe`t{o4'
    'd3fjT9LaSCWi(JWp!a3$@_|g0HVcur4JY|{tpBj`@h3||N6Y;YzkPmf6USq(O&E=WykaU_pwwu*;'
    ';sV^3o1&6+}*R*pagcok35=UTOmz1h_qn*Ao{evbZtwoMHQ}TO`6>8{7lU1>LtE24-'
    '{ezrMu|h3zq!HDd@<l31osQ#cvhwPU^mOe{&qr#Y~%_e+%i8)-'
    'QS|4q7d5h%!J>rLTjSk4jwCw|9UQS8byf!v%04lzEvBUrSp*JOVr}mI>;2`lnL5;Uw=dKj3U@@@t'
    '9JmEv`y`OOw#GJK0(IAs4RO1o5KyLR6qP7ApdvB5y8Vt0G9#2|+ZfH#eYTrd$mi%VM&G|0#8@ThX'
    'Z`);1;c97s%aaG%;qit{q($rs$G5tL}XY<35RczU2!KFchPvM0oK}Jui2F3RxF=x?RUGzTNF3$`3'
    'KaEJ&Ang*7Ea>h7UZP$CsZRt)qsecZy=%!<#{v6Mu%Yu`iNvfB<P`$PZ@|m~K-Z`8{Bg-ISc+|uP'
    'W%M3-gJQGrWBdIU(<~nKufW338u|;FiH>8T`~tHvfsK4*?67YfLEZo1d)i6-'
    'l(=O%M%%p2Uu!)+F{xdoOXBPQMMQ^5HRu~-'
    'BBCZ(z9K$i}WfWaLxUvp4cNJv8ByWtFpZGud}t0{ZR1-'
    'xs*IZ)1sLq%6oYfQw!On387>dHCQWk!0T%1MYKoyweE05sV!;v1nxsAn#BFimH~z7RUU7Uy(&+Wu'
    'HB360;f-'
    'Z=V{(z`1yu20Z=t_%}v|I=JUJiP_j#8UuZm#82jm)LAPK{K^&N5nX|r~fhdL`FSG|0Hsdm&S;RwE'
    '??Otsp|8f3`JVz?2cB~>uNS#xb`#%xRZxCK;wBcuJ)`NpqU6Q5N;+B?dqp@9{4*G5ouPRs``@);h'
    'VKAsyJDA$+c|VZVHp2cn-cgITz$C)b}xN+?T~5=@i<glbPM&?%1sellbFdk+L}uh&%Dy<cC4ayhI'
    'OOogn{Gw<DfaPhC#w9Ukr)dOqFvaPZ#Ml>>QrPoJWUqk6W<ed*^^+>ELp7$CyOn(C3BEwi+=QtQN'
    'M-W(aGMef$`VlG^P_&kSW>5dj}~-ii7_lq)w?lqSkZcKdQVplmIk@RdbdsbE-hEC}5*2@UBz{Q80'
    '16p%!bMyGg!I)wgP!tqi*&T<eTL-E1mWS=;8;zhCL*$-'
    '3Vgk_|hhxfd~4WUpPC+jngc4lE%?~m4T(!9H+l(14B^#nrfWV@;BfHSN|yQJ>A5UY(;Gi_18tJQt'
    '>)Hy=!ROnoaV@XEox3fxIH>jpH{|GzKikK2c{!zJfavd{1By0H$Mrq)S9W4}eaP%6i3`97_y8z-'
    'YK&?9kx=U82Mzg`OV)a}~B)OSO`0;3CkPb(?#2FK+u+8^0i9l&bI2qrFvZ1^XSOQcMxl`ib#ghTr'
    'e9Apzjb-iL@pRg-vB<O$@s`tW5?+!GiET>W&jf97jdRT}88s?38I@?*Jh0Jz-'
    '>5+Igobv;!z?5Je2&az5E)gQm04|aqIt&xg7sk!8j^GGfpnF>ln_8yk=LmHQ3lD<mqr!`cmaYE)!'
    'H@2TmDDMZL{h<tf+-?rkUKB)vUnVl!4;YyxxNR@lc({+BV2~F=^grug;)y#Az4{)!VVd-'
    'd+}g<8oM+2Mc*ePE6lVLE@jRtJUvoCG$|?VhISUH&y60#q{he`Bl)Hz=M1k<j(7+z{%v-'
    'j;KWxB+p@qY>i0|Rk|{2fjL0?S7vG#&3%4uBUg8m+FqAy^_se)$L{18UvNnVJHpxylwe$>B%zld?'
    'DlFCHkir$KZvb)-oD}9c-'
    '0Jm<RLro;P@Qv;lFb|4d^QTAdc8{S6Jh7@qT>7O30Su&4)R52%mef5L_BWM(q@D7WHZu#L=vv?NL'
    'ANHsB>55^(`4?z@@D1ZlGiNJI5slwSs?GHocNqmIYuHr3IUzYn>98A9er<1&kbI8wbMu@wJu1kg)'
    '(vqRr_|HiAiU`ycp4Ts!_$p0U;iu*s!E-'
    'mI1dSV2h>L~l@oT~ynnMYgc&L+geRUZp1a{FsDjP2iErE)A)dpr_3*XXuWe-WpP6{h*jh21cCKf@'
    ';csZbB#DHv!j<B`GKXZhew9#0PE4yW5+u%k`pq~~vS+}_pf(vsyc8a0X@Xy)i0PH9nkirXIABnu3'
    '7reAk8z4YTW{)y6n{e#00<Q>UJsh!DB;24Q?54>~#?{a6+KW2u(vD}?!-'
    'R>3}fR}b1xg6>GCx5}f^uy={D~V$98_zi<drS44>aw|~nei`T%Cc@3u=}L13}i8CTMu$thCB{E@e'
    'Is&!)$TI2SBbB<@W^l2CAn@#Dzux+@tx3&VTSrKD(6m&A>kA#$O#r=#wjB?_QzRK5t2lfS1kF-'
    '5qcn)M;>%aWC=Gf@AJjzbXA(lJB0t4^<$X8fvp@zX)Uc{J`{y!xEp>?XT9R%D#k`l20VqcNGEARR'
    'A{B8lOg@t?kL!=+#{;3kSoJ82NVrgv!3x2A37hb1r*3-'
    'G5G%(U$EA!fArvR5(xz5Zz4}5;#N&tjT{Xad4y&(kO?b=Is68IVp`bBiXftYKPTj7Xi>U6ts-'
    'X6{4i)V!lTnURMjf{!d1NI+hfS(OdtzILuP1^dx3iK|r7Vr?)ziM3RK+NwlTK714jiNt`vFCXj^k'
    'CMYvQD4M5nCkji&fJR~7jHPYmZa?$~Ji0|)$^{pBYJ?8>b^$F}S07CxedPN{x?J}_HJi>~e`~x<D'
    'm>`SKQ;#Zl&X6bmww*f@_SnvOQH-_dwC9*6qB)koc`<G8(!ls(;{}{kZ;o9=EWdfYvC%p)z?{mfz'
    'XW6V@Q8+n^TNTiOJD}U>u?MxKaV({Lb_PRb?iyS3b=LDp1rW1#o7U5iC@O{{$mgl-'
    '%jRY<cz;cw=Qy&^HKv0smavzwp5*Yc`K#<AqDz657TI<8|h-'
    ')O_~DLLVc<*k_(YFJ?!|^%awggr2=aK)_tFq&(Aw6J8U>D$i{z^Uxxm%<xXDc5iS~F<$aRt!)!Us'
    'Q<^?!i!AawKZ9LpNuzE{{0i1$CWP^eNsPScabQ***tiGCM2Q>CcM^vto!7^8w?IwVV^F+Kl)XeYE'
    'gZ=IMhBVg5gp9;ADB!(MX0V%&?L$$@f%@Rn_jEHfZp;)?F+mZLcE9oR_X1Za|%Epm}+vryu6z^L9'
    'eGw~jpQR0~tb7g18Uxht5vvphTFWGOJkN#DONAL}J5EjEmY|D&yMo);<u58sm3+7aO3ihD0@I<k~'
    'L&(>y-V9zF6NcBH#%?gVb*^LJ0vaHk}0P|dNs?H0N&hD@;BBNt^LK_${8br-'
    '<e5F<EpDH^x_at5v;V)*pbW=?2gEN71*_Pl1H_8gnG$g`Z&7U~~k52E%;l?Z$!v&uQHV}DP(6)aQ'
    'FO00U0BWzF=3f#0=Abj!SG~}rPJ7f0ZVC%J_HQcC`5|}GaCOIlCWo$xVp(T`Fc5Cjl}goGb|f>EB'
    '@9&HE7xG{?uXHdN~;QWDE_Qd0Xe*ubyr!*3O?JU!Nnp320u9&QMfusBT(Z$P=kmw`svEwARIzc!j'
    'g{1;<{T&pL1PvC`dG-<@&acfvL!WgwE%MXJ!7eJM>m09+mq1c&nG>|3|&P5iqO-'
    'Fx(8pK`f5ECAeaV-IxG9a%Vo}eVE7ZyoVk(My|Hd7td+NU1QbQ`RjG6y}KHznpfQ0zJ^hT501_mX'
    'QaTwTxLp6?9u1^lF=ubkTUy+QaSEy$(Bbb?Gf6QMbowz--KnY`BAq4fzctvq?sgf3I^er0nrS~JC'
    'yzgtH_Sfv{bNO5A=eQ${~-h-'
    '02O_qxt2Qey2Cwq;4%dN7=5wS;H{n69#NmV9SQCh#_$@V${!NMc<;1_-'
    'VZ>D6TA@Z?B_t99Re^ftSKk7$0xVS`2Pc?-$kds4y8-'
    'gLia64Lp~<BcSU34aut@I0XURRAPqn{G=ihlo=*YU2QsdvZTTS+A8Mf<KH*4mHg=ORBhqo7m!_S$'
    '*_YVH6M6_l}l(7ODPLDot)m;M}o0&$I_E=g3iWq-&-^-'
    'U8u()P#1vo{H&ODV~Xt|vrmkEHbG;c<^`jhHTtjpt+v<TcB8oKs`6!WjgpKzW~UZqt*-'
    'deQrvM4w<Ci+UF!XS*Yp(mC7(DOrE)}D*J6G~IOY;-'
    'UeYvPlTLSf`GR`|2Pr+LQ~$fYEb3M5p+tg{0(Nb(oGm68y2s{DsRK2zfnoez8nofp?&-'
    'p_rhB&;rNFiSq&?Z?N!!c=7mz4*hD)D{GZZ#OlGS$d)A8QreEXejn^<YD$5EgnBIl4<PKgmg$7X@'
    's+-'
    '0zPh67yos*o}JEehFb)KU>Tq8mgPYk>;=B*y&_(f3_chX*o1Ni+WaYctwAwPbSq(P7bth0^{)wr}'
    'C6@^Cb!#?-'
    'G|NpxBN3)M6zPCc&oIFZoZvVRt4Ed8<k<6%}&2z8#x_zVv84Juq<kR|!{@i5GY+iS!6cXX~nw>w2'
    '=N2dAaFP6`bu7Vn*29O_sNGq4Qv;0BRy@}I=!woXYXMAoxd?X9+1;?}sl#my&Luq<A&cUQgexzGm'
    'M@c+eCxD+GR;C>_{}Q@XGk#YGnXEZs<KF+Ox1GqkbxWie&R^>AOxJ2Ir})4uW4$#seipg)@2>Egc'
    'lf`01bC22!qNgP$UoopK5iBh5PoiL#W(Ql4BNSMf`fs#NnrBI)<s5mc3#+NLAoQ$53qVHXmn(h%Z'
    'eg!IB6ZVXsgdFoeSM^3>hL2>5hu&y5J8xj}LAH7U}ydx^faYecqBtI(Z_=W+Czj;w?@!wn<s6F~%'
    'c1KkL^eGZgUM`bbQ3yP}7g*KYrO!@j*JOcGC;yzy1{%)a^L;}8zm4B{+l&{QfC_81#@;i!k@?4UO'
    '#EKr{T26!J@ajk8rrWAnR<mv)LoS@i|TIe>Te$bdK2Q}6h(&<Bb+fIXx_7M!_^%ORKGucD7J;&`h'
    '=$SgakRYTR7yOR?44!>c()#INs_Zs`PoU>qx<z<@adJq>&cXY1h240V`@i!R;GELuLTQtxhLLTN9'
    '3)NjLehEP5gAPV`27RjhXpciQcbz~NQy1h_21h#*2wqqW&E?l4cDh%`*0@9^ZQ^5O#Y0l6xv&0_@'
    'jhal=~+5B*S|UK%Z<hR6EvNr?M1yD<?p**qmN4@sQ`$S_=#M{xi^v=2f}vh`)4r=*2F7NTndzq@Y'
    'worc+EE)y44`+MiiqixkomUKHt2?jdt@mk-`{e*N2~1Gidjw&`Jdb7!_X+F4_ijo7vSi-'
    '8PpUN<7-'
    'UZ+V|=;KP{Jr69A$=z*{gkDC=1LSXE^U$%k_wHwOX1iAV5e`*d)Elz@so!l6rh$g7=*1k#pHacYV'
    'u@zFVo#LOh)4*D4;RZXh$8~kHD0p0p(ObI$#OzDubGLxK8kl2vvO+-'
    'jx8p(R$ogfua7S}SSAr^!kxdks>MVUMk_LTAB;s@Q|7uWQaijn=oJE+;vfCJU(09zl8T4@!v+Vc<'
    'Cg(k?y8{(`$MO6&-PEw+^}^Omn0kg{N2a$pcz;ZEs+|mtBp#@XAN^*jvU@b9wEu)k#lel!X0sg-'
    'U6Gu>UtPsuvdvUzGe+2VymuOvD*v}C0N&vjc+fhDTE$CdoNboYiQDd$g!kYYcwg4R`OfY(r$SvQx'
    '47=Olzz>fSZ35yG2{kTql@?ABPui(ELRuTP9$ooYJ$&M$%5rH3RF?MsP$|dU+LR27ca1;rsbBqaJ'
    'M-o;8P8EQe4wH_OFIk>aIFCLf1v@;@@kJuRnouHHZ3-'
    'hkgB4nlpcvNR$yi5qMz$rL|U1G+)2^@=z!#iaoP&VDsz;<dQMLMODDSH`%Bp{KU(-'
    'j$oQspys}<k&-4RzP48Lv^r-'
    'R+rVNGWCkb2L%J@Li2IAgVwJ&Jb!`~jg9WX_@b%IOsIhzu&5I|e&W+nEJlW+gw};xlCe}`oqg|?s'
    'Y{Bp_sZLlKe6#6(I-OK{Rk)Pdg>y;63u1M<YfW-'
    '&KR{>qmtWPA!WZmfaX`k44BO#d3YLTP}l9TT|u^^qy!r=m3!xCU7o`zC0dot!n40ZhHJ$K#t{AV*'
    ')IZnpw-'
    '8(EoSN%PRp&*!odq@!p8Kiwa0pShN*>CZ<wWrFzUxSOXSMuEyNeV@Xjikry*A9zvW0vYP6-'
    '*g3Y78=JqLePv@W9Iu6xUwz<<Q_y9%q>KjRK@q;Rw36hNbt+eFL8indzO{h`0Ra*IMp3aAE&JDz='
    'EJ`=#?(q<=E*VB~hL}WNP1WY_-'
    '=XOW51@)PtOrK@bm@eEG1nAEVWhv|>V)Ra4jp*uV#_=sL<@ooUP)9uQ167I0-'
    '`%eX9{gJu>wJX(ov+;rRS%Prr#1cvK>#A=}ws|p?ukduIBA|cp}h&ID%+#dysZiL=)Ikk+RA_OGm'
    'Q-CDle0O0WsKZE51}fNd?@IVWjigoV*eY(dGnuxwt;WLLfsi8YL$$s3iyB${-w^hyH^YxuN+-'
    '#mC|+1lZm127M+X}+F{zBq;(?$<4XQj1ikR3g9w6=CCxKI4o=V-'
    'T_r2KBN%yIdg&iQDBYN%ebR@=UbqtJ&iuvyAdX3*NjV-<d%(W)Y&3f4#z2e_><L(kk;wa0?JU-'
    '7bbvLHp^I-'
    '9hOkIOo+h!e0uOCk)As6^(Q`Vp?w724Q1p#qljZf0YCe<M!Q7bp#RTgxYO7<is#@x+`w>%-'
    'l;StRXX6k~v-aaD}TQi`cr_2)j_&VgrD(=zce54-'
    '*Ct`m$+_D9G+eN$oY6t0;`H_=|Kil7+V`lVbkX--7O}a!dg9P?Fncae`eCIGBPr7gXl<n8~(Q&&x'
    'Eot=^&alGMPvShsmhRvcp+(JPBx_K9+KNxrJP)MsFelQJTQ&cNjEa^2+{XSNe1h#!GUj<GXLh0wB'
    'S6}9jn)3Ky9mAg2!6gzdM%}#t@3*=ZF<)Ni}6qE9PKC}g5+<qjB-'
    ';wp0$TkDCRS(7236d)e*SXNeIzK%kbEQ}6!gn;KhT(@>D19$AuZBur*Mq#JC^z;IyeiOqAZH&QI('
    'YB9Fy%?7g7u}Whm512X*`m7jM$I5IHAk*c`E3aYT(nGCD{xLkj7cJG%expj&3&u{TA6R+P<&DUx7'
    '+9wK#e2|AMFLxLG(xa=mVWgHZ>%efxzxxVys8&eX+y^(cEIk^vg#gT@uYjqm)aprqf;?77!FDZq='
    'VXJna7JhVKH*1T|g@}>KAj?HeTnyJu(=-~DrNg=rpP4~hQM`ox0-'
    '!*ES|6}(1`uEIzIcW5~Gd4?1XJrq;=y+q)d%Z0fC={%U6T*}Y{Vs#8d}1yc(%EN5pRC?zS8G~n$v'
    'mRjsr$TAxFNH~gdZ!w`+7txzqKu7#L9AWmpQh>j6b3i`1Ju`Q6s(W&)YGy1=eju_@gwN^gI=ihTY'
    'kpjhm9gyCH?k(;aSnya}Q#=B_BP_(rglp#AOrAd2Fw(d8CRHeE_;7l<wn%qD;cxp2${=4uQ{!&Te'
    '5(TtGCQL~ht#cL-Vl|M^7e@vBv&UXhxO7C;2sz^1eivxTPr|t=z`RFzV5328ld047EV|?Vh;z<am'
    '4u)SEN_pg)cz5*VP9ok*zB}@`xh<Uem3;yFU|dA|{*ZoAS!QkfHR&f)3vXN1X9?4MWzt7IYRM3L%'
    'f0cSu1$eZt;^tGY^?zZCv_)PvZ{3363ZyfeX}!tWgI)*HOGX-'
    'T!epSsRVKst&ED$eDt7zrf(Xk?L6LdB;tVw4oeFr@3Aub_Eb_*qMV6F+JIR!Pbb%`RF~fS&%`VgE'
    'AMb-'
    'Y;N?_^y#>T*p6J?IfWTmEPW4?Y7)(R8}O&{t(i7OgS9=BFeCf(ydEf1&ogLd(DOK@Yo3;j8Tu-'
    'q<G82b&ZAh9;+2R7HK_YiK%XD)SbU#LoJkXgZFmn5Bl67@-J83QG@w-'
    'ytU8<^r`%L80Ehy`QVE;Ai?a$UHk}H0-P>F828=WIWpqDQle~X_XR|-'
    '<SuBu76n*!#x`8$!U#{Z*N!S7wN30_e7>UAlj|SfSNwKaF1PJ+e8tUO?fUKE!071BaE>q8+&x<ya'
    'EJPlRb4Yrem^rM|rPhOs=k{D%adkMoY3=T@wSqK0rv`*QOhE2=gBg786JcQ>%AhABmcxTsoNk$MX'
    'yS=}GoTuY^jEnT3YWc<-'
    'WTOcVo@I5nXE)wm%Bg)982i)I{opLs&^^NDB|^f$oB~cyGJ}=hroSa89ky$xd5iZJmWozz%a_&_b'
    '%d{_LL6kcV>trDW_5@T>T}`CG5SJK;@t=BP^mcESGrWEepGJEo)j27#v?debVs)<Bdy*<NuostOi'
    '~&!_kq@TfG1wcFPWfjN?%@ew)3oXyBO1kAD|2Ji>(rqdfr{0nCj*t7tgqgB+ylEIl%lJH<|V03ZT'
    '@X5J3~(tc4ia+v@%rfy=P5EXnZT>Hr9yx_PE2O<h;pad2T2wlODfw39CY*=M@GsvpQkJ~#IT5u)%'
    'Adh-uo16Ej=$g~m<%^8wtwreESY$G19K6QhW&Z=t5|Gek(E8I`Dm10=r6VTeQoMuu8Vb8fzXF>KQ'
    '?5V6l6of&94FM2c{0$(6qG@$jjRTHevgSO{34Ke8BQ4w_|KBBwch(~BAR!r1Fkz3eg?uLqfj3VxO'
    'l6nNjO%@Kz_s6l49On@}2?jWmT5Y0uE>(VNL^9paJ++V`l<i(U+c}@B3;Zp$)DlU(B_9-'
    '<RCN^uzhdb%MdQ>WD!8vUcfvRnF+2k6hG}a>ZJ6N$suz|4UvjaT!9nc@X^t1eiFmfw#?t`kX&6dE'
    '(2X;y;>O01(+2c{s;qv&SJx=jA_o_b-GOo><K%OO`#rbpD--8|Mcfs3Z>m{fCjy`(FsYN_mRwWy<'
    'P|j&nZ@$@ih88VGcdVO^5+uV)zqhM*4${eB2_EjULfBGyQ~#~|7&_~ZmoGf4j~?ge#>;N`9mIZ0q'
    'AT^_7o&<jhAm_I?h)xc-'
    '(>Gr9Dt=z_G%3me=?+Wm;c5yxK4t1lAcl{T7&0J7&t+|$vxH`qSn75<<OcWelAdQW^5A*;z)Ywxk'
    'IHYu?5kEOu^Bmw_k{JpSELH^=-'
    'q|J!$!r4v8F{gq#R#QMf?w|mzlDbd*&vaOt=NXVr2_UQE3EUIu4>$|hfRO{7{+k=Fzqz&F4egMZ1'
    'zHlTM`vunky*~??LmI4~sGA&PU536yt^WawkI+Jj^a-ikFeHRx+ZDV?MRMF_tQ{gjMj`5pyT-Bb0'
    'GVLT2<}^{Xwj<cyz}U<*QpaSf&Teu=nm2RscE&Ps-!2~DTu*5`&YxikHJ@FjdFhp7h-'
    'B{(35q8U&r781TuSOo>gUl$9rC^ewU%@utN_!W#~Mzh1sg&7aJ%{Btvnk@5r=|?gRPjf-'
    'tdMxcyrrGQ)FubQILQeuO=X`J@N(ZtHU<tB%l_JdWbgXPtEbV}mO&}f1GYznn_nh$>m(zT-'
    'pz=loQ!lag`Hm(>kt4F=(#})Rk5V&ti8s_%8)P*~Y)&(;1WZvvjy$~K(V{TzCa^`if-ZdT^T5quc'
    'lV|Pn(!Y1C~RBS!|ZzH%S}|RP9`>s=BXPcz%)i|pD$8)#^f2@$p;4Gi0xv*jZ%^EDcw$sjPuxnvK'
    '5<VfTTr@&Df}Sj)ugh3jVy)pt;HYfQRQl3!SG!(Cq1N%MGkX%=uuql)qtTGoI&eZ`P(CXS8jN>N*'
    'lG%^~<qF3Yrmj#KTghJ39+YT7<YcT>la;KJlL1E^IAS_?<F3m$J8_gLH6?b~@#HJv)~`qmo|$|@t'
    'XUeq@=Btrw|<w~MKvU)pOJ2T!UMNO)hqeii*nZ<{g9{V}{YG+PMe48`=cEp0r3(N?u(Y8+f9f4lr'
    '7|ce)Rq@PL;E&n&ti3J^D2+vV2$#*HE=e(iNRV&3aje8Hxi`!~S;X(BOQlVtn~*4Q>YPbz?NK(H+'
    'DVZ-ZG;j4S(r8vF_d<oM;8|^EL#u0Ui^(!{A`i$l+X;T>rVv+6q~B<TfhK55HK^SQl5Wqf;=2ztC'
    'MfOdQ#so(iFGg_Ok>K&WZ4236&&ff|*qiC4<a)(g0}GD_^yU^8fED($0;w=UT?moP4@nzqecW&;J'
    '*dAug%ajJ?%}V}aKTbR0Mh!!G-'
    'pqOc+oT<f?6HkDV?U|{0XS}*vl1Y&LA4oml|cJ?S(31oxaFkB*|Cyax$h|y8=#+*UDImbdg8$J?7'
    'W5AzY!&MJG2}aOWiFwlAo31VfiEkWgq*891wev4KN`ZWMX#M<!(BxhYsqZgLgZ#NLnMV#2gfl`!f'
    '8c|QcWY-vtm8OVxz;|m^}XX4`9rs5zfTL<pW^pw$-'
    'gN_?wQFoTU#qyc8@eS)j2;j1bi2ioa@vOPno^7F?QY{>!+Z7&kVtA6bK~c6a3MW;P!mZU?r-'
    '2HHN2Tl;|9fNgCi}jc<A~uB@ee78&8RA@Xz!#VtG!U7VzJW`yruV0PSmh-'
    'c7t;;#4@(N*d@B@L)Kb(;T4m_eBNH_Gro=G%B;0tT(E0e^qAOTKe8KZ&1VBn=MKccXf!^I6ouxwk'
    '6nK&U0Nq|nh<nr1$8&I}!GWz;kGiDl@{r53N=a(a5kE})Z#O4%?4$X*u!*JS2|bK1S~1r|A_&F$q'
    'w&jQ+$_IxVRx|fEES5IiSEnz4<WQ&d^!#&_f<655p&^W&}*8YY|o2n&&q+KVNaN6?zdB8;3o>jq8'
    'Hl)N9a;R)Sy18($GRQm~mFlMC+Cjp<ja$Vf``bqqQzM6u=WaKPF*uqO5MuRy$OYA=<*GGL6^#3;b'
    'UE0qvlq+XdJ5k&pU+xPNfglBK{bfdQu~#mf+7XvDc-'
    '0RJ<Kz^EOg)1B>(ES25%Nd=clF6n{?;i2`X_fhT&U!{hLV}r)=z@vE*8+lXWmGs7tUUKT}>LIybJ'
    '$FAqz`&2*5Gh(pQU8vsBdF3l88*m@L=A~O%lgOXikA2x`@(03E#V97(*o3^-'
    '6e}$;07;|6RdzgoEGo?H=MQIyud^$oHsUepzAmNquU}lI`k<=d@EV?E@Y5DTkKgY9oqOb8#BH_GM'
    'Vr&XS^<Jr>Yp>iS>=O(j5AgXb_zY0nG8DG2tIcE0eDxqbrIOxcqoy)3EV1>8d+Q0vgCXvb1`TV+#'
    '6dR(0whe!Mzk9fz$c|sg;XmUqpqLJPbv5t&v9#l8u><o2ILz(+!biYIb4Q_CIrcLp?0uHkRKq<BF'
    'yONg62#5R?yl9c|Ba_A;9r&zJ@;G|ApS0EIK(SRs)z07cdUl*KU0ily#?nO6WVgDt|1IKS5~CUE#'
    '=>uy7(p7LNdnkDwLkz3ki8_j!y)pjl26%g?ZYVxMuBv~9d#j)Tfy|Md@rbwl9es!ahCQ?})9{-'
    'SI(3(`$$^Mt?bnxlulOPG$!IRyXD9D>z#n7&P;Vxyaz(bWt_C^wlba*$$^#pa>mEB``lPaUu}tW)'
    '~e;*89=9;i_i7H^((YSRGytS*AjwO1>>_`}_$H)Wk)&|#)XT}qmN`}kt?M+iC8zwzMH!&N2YZP|J'
    'V$xp4FE(9!|b!pULp0I@q&E%bz%>5S?>XvgR8cr6|McTbq!#dJ8kh{a?_GQ(({7E2Hk-wp^;X)w}'
    'M&<FYGmr1Ao|mmipWVEfcZ!6)$iKLyii^u9P>^1k5qiEfJxFvA<7ksyt}X7`L-'
    'u@Z1+$v$PGKOXE9r0K0!;RidE!pNYp6u{(Hx*iVPhX=0U4hq5M@kCfd)pHgxo{p<38nqFg{N8Bo2'
    'o(XZ<FL{~P>NJQ_kgsUyfqHyr-'
    '@HLN?HG1X3l2EN32)}B=!Ob0T`YUqQ^>x5ww8XPE4pZEoy2^`57(-'
    'loW;4~Z%LJfYTDjPXfV{9~c-'
    'uM6SLAq$e>rKFcUCJkn0R!k)DyhSO4nv}G@XTW_x+Nr?JAO?qGoYP0qCsAF@B*vSfAAf7w+Mk?Hg'
    '|MI<AKSj+_3Pp0LMaDvBtmCdUIE6IMvEX@L+1!f=g|g!y8h)o<OhxC;U0=!7y}w7E&1knqS^X<&z'
    'q+7$1GfM_`(a%!m+}mLSe;d`WzIgEa|xzatKpo}NNPIhWoP93rZ99x$B@Cb2*l7Md;#{2W$qWQ~k'
    'B|EK4<$J}9#*8RE--RW)eE}jR^faBV1L(VwBK8*c~PT`bGWD|Q-ma*8L-'
    'GDZ>S4M;vz*x7|?MnTS3-'
    'UMd5i5*mGTDxvLQ@)!X;)8Fda#*CBP|S4qVoQ)Z4#?M4Bu$%h|hWAWXTmCAZ1}k0ox4eM<M&yOz1'
    'Ow#sFx;R^CE8!FvO`;CjQ<6*dN8%L^KuG8e#<BU0Oe>fH@xT9BqFRyb;CBQtbpiCK9o`K5Pdv+ZS'
    'Aq9=c(l1rh?5awma*dU=9i?R%C)*X}nZ}BOJ_)M7Zi0ebujP#8P&@KqxL)1QH0EAuF68p{WXD@%1'
    'Z0IQ%Gyid*T5)23t#O&316O$+XR5pNdHi&TK;*nXG)@|T2B@{O9l((ob>7En8Q-#?<6Wz-_IlAIY'
    '{@>@BhZ8d-'
    '1Y70qsDXSyYc~1|IvuC@2;b`r;w4_g**AV#WCQ^cuC@_9SfsKIo>kwz6~=C8oKa2h!FS)S%3LqZj'
    'vAXk-DaN_u}5L00Eq2nA`&Zw1o*0vBYQl0ssI200dcD'
)


# --- Exact canonical form, as in the checker ---------------------------------

def line_ends(lines):
    def key(end):
        i, (x, y) = end
        a, b, c = lines[i]
        g = math.gcd(x, y)
        x, y = x // g, y // g
        half = 0 if y > 0 or (y == 0 and x > 0) else 1
        angle = (0, 0) if y == 0 else (1, Fraction(-x, y))
        offset = Fraction(c * (-a * y + b * x), a * a + b * b)
        return half, angle, offset
    ends = [(i, u) for i, (a, b, _) in enumerate(lines) for u in ((-b, a), (b, -a))]
    return sorted(ends, key=key)


def general_line_ends(lines):
    ends = []
    for i, (a, b, _) in enumerate(lines):
        for x, y in ((-b, a), (b, -a)):
            if y > 0 or (y == 0 and x > 0):
                ends.append((0, math.atan2(y, x), i, (x, y)))
            else:
                ends.append((1, math.atan2(-y, -x), i, (x, y)))
    ends.sort()
    for (h1, _, _, (x1, y1)), (h2, _, _, (x2, y2)) in zip(ends, ends[1:]):
        if h1 == h2 and x1 * y2 - y1 * x2 <= 0:
            return line_ends(lines)
    return [(i, u) for _, _, i, u in ends]


def crossing_order(lines, i):
    a1, b1, c1 = lines[i]
    positions = []
    for j, (a2, b2, c2) in enumerate(lines):
        if j == i:
            continue
        det = a1 * b2 - a2 * b1
        if det == 0:
            return None
        num = -(c1 * b2 - c2 * b1) * b1 + (a1 * c2 - a2 * c1) * a1
        if det < 0:
            num, det = -num, -det
        positions.append((num / det, num, det, j))
    positions.sort()
    if any(n1 * d2 >= n2 * d1 for (_, n1, d1, _), (_, n2, d2, _) in zip(positions, positions[1:])):
        positions.sort(key=lambda p: Fraction(p[1], p[2]))
        if any(n1 * d2 == n2 * d1 for (_, n1, d1, _), (_, n2, d2, _) in zip(positions, positions[1:])):
            return None
    return [j for _, _, _, j in positions]


def general_arrangement_type(lines):
    """The canonical form of an arrangement in general position, or None if
    it isn't in general position."""
    n = len(lines)
    crossings = {}
    for i, (a, b, _) in enumerate(lines):
        order = crossing_order(lines, i)
        if order is None:
            return None
        crossings[(i, (b, -a))] = order
        crossings[(i, (-b, a))] = order[::-1]
    ends = general_line_ends(lines)
    cross = [(i, bytes(crossings[(i, u)])) for i, u in ends]
    cross = cross + cross
    best = None
    for start in range(2 * n):
        for walk in (cross[start:start + n], cross[start + n + 1:start + 2 * n + 1][::-1]):
            table = bytearray(256)
            for k, (i, _) in enumerate(walk):
                table[i] = k
            form = b"".join([order for _, order in walk]).translate(table)
            if best is None or form < best:
                best = form
    return best


# --- Exact search for 8 lines --------------------------------------------------

def norm(a, b, c):
    g = math.gcd(math.gcd(a, b), c)
    a, b, c = a // g, b // g, c // g
    if a < 0 or (a == 0 and b < 0):
        a, b, c = -a, -b, -c
    return (a, b, c)


def no_vertical(lines):
    """The image of the arrangement under a shear (x, y) -> (x + s y, y), of
    the same type, with no vertical line."""
    s = 0
    while any(b - a * s == 0 for a, b, _ in lines):
        s += 1
    return [norm(a, b - a * s, c) for a, b, c in lines]


def cell_lines(lines):
    """Lines y = m x + k, one for each cell of the dual arrangement of
    `lines` (which has no vertical line): points (m, k) on either side of a
    point inside each edge of the dual arrangement, closer to it than to any
    other dual line."""
    n = len(lines)
    dual = []  # p m + q k = r
    for i in range(n):
        for j in range(i + 1, n):
            a1, b1, c1 = lines[i]
            a2, b2, c2 = lines[j]
            det = a1 * b2 - a2 * b1
            dual.append((Fraction(c1 * b2 - c2 * b1, det), Fraction(1), Fraction(a1 * c2 - a2 * c1, det)))
    dual += [(Fraction(1), Fraction(0), Fraction(-a, b)) for a, b, _ in lines]
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
    result = []
    seen = set()
    for i in range(count):
        p, q, r = dual[i]
        points = sorted(set(on[i]), key=lambda P: -q * P[0] + p * P[1])
        edges = [(points[0][0] + q, points[0][1] - p), (points[-1][0] - q, points[-1][1] + p)]
        edges += [((P[0] + R[0]) / 2, (P[1] + R[1]) / 2) for P, R in zip(points, points[1:])]
        for em, ek in edges:
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
            while e * 2 >= nearest:
                e /= 2
            for s in (e, -e):
                m, k = em + s * p, ek + s * q
                if (m, k) not in seen:
                    seen.add((m, k))
                    d = math.lcm(m.denominator, k.denominator)
                    result.append(norm(-m.numerator * (d // m.denominator), d, k.numerator * (d // k.denominator)))
    return result


def simplify(lines, form):
    """An arrangement of the same type with smaller coefficients if rounding
    finds one: map the box around the vertices to the unit square, scale and
    round."""
    n = len(lines)
    xs, ys = [], []
    for i in range(n):
        for j in range(i + 1, n):
            a1, b1, c1 = lines[i]
            a2, b2, c2 = lines[j]
            det = a1 * b2 - a2 * b1
            xs.append(Fraction(c1 * b2 - c2 * b1, det))
            ys.append(Fraction(a1 * c2 - a2 * c1, det))
    x0, y0 = min(xs), min(ys)
    w, h = max(xs) - x0, max(ys) - y0
    scaled = []
    for a, b, c in lines:
        A, B, C = a * w, b * h, c - a * x0 - b * y0
        m = max(abs(A), abs(B))
        scaled.append((float(A / m), float(B / m), float(C / m)))
    s = 2.0
    while s < 1e12:
        rounded = [(round(A * s), round(B * s), round(C * s)) for A, B, C in scaled]
        if all(a or b for a, b, _ in rounded) and general_arrangement_type(rounded) == form:
            return [norm(*line) for line in rounded]
        s *= 1.25
    return lines


def to_infinity(lines, i):
    """The image of the arrangement under a projective map taking line i to
    the line at infinity, and the line at infinity to an ordinary line, which
    replaces line i. An arrangement in general position, of n lines in the
    plane, is one of n + 1 lines in the projective plane with one of them
    marked as the line at infinity; this marks another of them instead. No
    three of the n + 1 lines meet at a point, so the image is in general
    position too."""
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


def extend(lines, found):
    """Add to found each new type of arrangement with one more line."""
    lines = no_vertical(lines)
    for line in cell_lines(lines):
        new = lines + [line]
        form = general_arrangement_type(new)
        if form is not None and form not in found:
            found[form] = simplify(new, form)


def search8():
    """Arrangements of 8 lines in general position, of different types."""
    rows = lzma.decompress(base64.b85decode("".join(BASE7))).decode().split("\n")
    base = [[tuple(v[3 * i:3 * i + 3]) for i in range(7)]
            for v in ([int(x) for x in row.split()] for row in rows) if v]
    found = {}
    for lines in base:
        extend(lines, found)
    # Then mark each other line as the line at infinity, in the types found
    # so far and those this finds
    forms = list(found)
    k = 0
    while k < len(forms):
        lines = found[forms[k]]
        for i in range(len(lines)):
            new = to_infinity(lines, i)
            form = general_arrangement_type(new)
            if form not in found:
                found[form] = simplify(new, form)
                forms.append(form)
        k += 1
    return list(found.values())


# --- Floating point search for 9 lines ---------------------------------------

def float_cells(lines):
    """Points (m, k), about one in each cell of the dual arrangement of
    `lines` (which has no vertical line), as in cell_lines but with floating
    point, and the dual lines, as arrays p, q, r for p m + q k = r."""
    n = len(lines)
    A = np.array(lines, dtype=float)
    a, b, c = A[:, 0], A[:, 1], A[:, 2]
    I, J = np.triu_indices(n, 1)
    det = a[I] * b[J] - a[J] * b[I]
    p = np.concatenate([(c[I] * b[J] - c[J] * b[I]) / det, np.ones(n)])
    q = np.concatenate([np.ones(len(I)), np.zeros(n)])
    r = np.concatenate([(a[I] * c[J] - a[J] * c[I]) / det, -a / b])
    count = len(p)
    D = p[:, None] * q[None, :] - p[None, :] * q[:, None]
    with np.errstate(divide="ignore", invalid="ignore"):
        pm = (r[:, None] * q[None, :] - r[None, :] * q[:, None]) / D
        pk = (p[:, None] * r[None, :] - p[None, :] * r[:, None]) / D
    # Position of each crossing along dual line i, in direction (-q, p)
    T = -q[:, None] * pm + p[:, None] * pk
    T[~np.isfinite(T)] = np.nan
    T = np.sort(T, axis=1)
    em, ek, nm, nk = [], [], [], []
    for i in range(count):
        t = T[i][~np.isnan(T[i])]
        mids = np.concatenate([[t[0] - 1.0], (t[1:] + t[:-1]) / 2, [t[-1] + 1.0]])
        nn = p[i] * p[i] + q[i] * q[i]
        em.append((p[i] * r[i] - q[i] * mids) / nn)
        ek.append((q[i] * r[i] + p[i] * mids) / nn)
        nm.append(np.full(len(mids), p[i]))
        nk.append(np.full(len(mids), q[i]))
    em, ek, nm, nk = (np.concatenate(v) for v in (em, ek, nm, nk))
    den = p[None, :] * nm[:, None] + q[None, :] * nk[:, None]
    with np.errstate(divide="ignore", invalid="ignore"):
        t = np.abs((r[None, :] - p[None, :] * em[:, None] - q[None, :] * ek[:, None]) / den)
    t[(t <= 1e-12 * (1 + np.abs(r[None, :]))) | ~np.isfinite(t)] = np.inf
    eps = np.min(t, axis=1) / 2
    eps[~np.isfinite(eps)] = 1.0
    m = np.concatenate([em + eps * nm, em - eps * nm])
    k = np.concatenate([ek + eps * nk, ek - eps * nk])
    signs = (p[None, :] * m[:, None] + q[None, :] * k[:, None] - r[None, :]) > 0
    _, first = np.unique(np.packbits(signs, axis=1), axis=0, return_index=True)
    first.sort()
    return m[first], k[first], signs[first], (p, q, r)


def integer_lines(m, k, signs, dual):
    """Lines a x + b y = c with b a power of 2, as small as rounding allows
    while keeping (-a / b, c / b) in the same cell as (m, k)."""
    p, q, r = dual
    a = np.zeros(len(m))
    b = np.zeros(len(m))
    c = np.zeros(len(m))
    todo = np.ones(len(m), dtype=bool)
    for e in range(4, 31, 2):
        s = float(2 ** e)
        ra, rc = np.round(-m * s), np.round(k * s)
        rs = (p[None, :] * (-ra / s)[:, None] + q[None, :] * (rc / s)[:, None] - r[None, :]) > 0
        ok = todo & np.all(rs == signs, axis=1)
        a[ok], b[ok], c[ok] = ra[ok], s, rc[ok]
        todo &= ~ok
    keep = ~todo
    return a[keep], b[keep], c[keep]


def batch_forms(L):
    """general_arrangement_type for each of a batch of arrangements, as an
    array L of shape (B, n, 3), computed with floating point and packed two
    numbers to a byte. Wrong only if floating point misorders crossings."""
    B, n, _ = L.shape
    a, b, c = L[..., 0], L[..., 1], L[..., 2]
    ai, bi, ci = a[:, :, None], b[:, :, None], c[:, :, None]
    aj, bj, cj = a[:, None, :], b[:, None, :], c[:, None, :]
    with np.errstate(divide="ignore", invalid="ignore"):
        det = ai * bj - aj * bi
        pos = (-bi * (ci * bj - cj * bi) + ai * (ai * cj - aj * ci)) / det
    idx = np.arange(n)
    pos[:, idx, idx] = np.inf
    # The other lines in the order they cross each line toward (-b, a),
    # which is the order from its end in direction (b, -a)
    order = np.argsort(pos, axis=2, kind="stable")[:, :, :n - 1]
    # End 2 i of line i is in direction (-b, a), end 2 i + 1 in (b, -a)
    crossings = np.stack([order[:, :, ::-1], order], axis=2).reshape(B, 2 * n, n - 1)
    dx = np.stack([-b, b], axis=2).reshape(B, 2 * n)
    dy = np.stack([a, -a], axis=2).reshape(B, 2 * n)
    ends = np.argsort(np.arctan2(dy, dx) % (2 * np.pi), axis=1, kind="stable")
    end_line = ends // 2
    end_crossings = np.take_along_axis(crossings, ends[:, :, None], axis=1)
    rows = np.arange(B)
    best = None
    for start in range(2 * n):
        for step in (1, -1):
            walk = (start + step * np.arange(n)) % (2 * n)
            table = np.empty((B, n), dtype=np.int64)
            table[rows[:, None], end_line[:, walk]] = np.arange(n)
            form = np.take_along_axis(table, end_crossings[:, walk, :].reshape(B, n * (n - 1)), axis=1)
            if best is None:
                best = form
            else:
                diff = form != best
                first = np.argmax(diff, axis=1)
                less = diff[rows, first] & (form[rows, first] < best[rows, first])
                best[less] = form[less]
    best = best.astype(np.uint8)
    if best.shape[1] % 2:
        best = np.concatenate([best, np.zeros((B, 1), dtype=np.uint8)], axis=1)
    return best[:, 0::2] * 16 + best[:, 1::2]


def search9(parents, write):
    """Add a line to each arrangement of 8 lines in each cell, and write each
    arrangement in general position whose form is new."""
    seen = set()
    for lines in parents:
        lines = no_vertical(lines)
        m, k, signs, dual = float_cells(lines)
        a, b, c = integer_lines(m, k, signs, dual)
        arr = np.empty((len(a), 9, 3))
        arr[:, :8, :] = np.array(lines, dtype=float)
        arr[:, 8, 0], arr[:, 8, 1], arr[:, 8, 2] = a, b, c
        forms = batch_forms(arr)
        vertices = []
        for i in range(8):
            for j in range(i + 1, 8):
                a1, b1, c1 = lines[i]
                a2, b2, c2 = lines[j]
                vertices.append((c1 * b2 - c2 * b1, a1 * c2 - a2 * c1, a1 * b2 - a2 * b1))
        prefix = " ".join(str(x) for line in lines for x in line)
        for t in range(len(a)):
            form = forms[t].tobytes()
            if form in seen:
                continue
            line = norm(int(a[t]), int(b[t]), int(c[t]))
            # Exactly: not parallel to any line, and through no vertex
            if any(line[0] * b2 == a2 * line[1] for a2, b2, _ in lines):
                continue
            if any(line[0] * x + line[1] * y == line[2] * d for x, y, d in vertices):
                continue
            seen.add(form)
            write(prefix + " %d %d %d\n" % line)


def main():
    out = sys.stdout
    found = search8()
    if N == 8:
        for lines in found:
            out.write(" ".join(str(x) for line in lines for x in line) + "\n")
    else:
        search9(found, out.write)
    out.flush()


main()
