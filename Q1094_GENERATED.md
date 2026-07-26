# Q1094 exact descent computation

## PARI/GP
```text
PARI version = [2, 15, 4]
=== 17a1 ===
disc = -83521
j = -35937/83521
tors = [4, [4], [[7, 13]]]
rank = [0, 0, 0, []]
#ell2cover = 1
ell2cover raw = [[x^4 + 10*x^3 - 3*x^2 - 4*x - 8, [7/y^2*x^4 + 2/y^2*x^3 + 13/y^2*x^2 + 40/y^2*x - 5/y^2, 17/y^3*x^6 - 17/y^3*x^5 + ((-7*y - 170)/(2*y^3))*x^4 + ((-y - 255)/y^3)*x^3 + ((-13*y + 85)/(2*y^3))*x^2 + ((-40*y - 119)/(2*y^3))*x + ((-y^3 + 5*y - 170)/(2*y^3))]]]
cover 1 quartic = x^4 + 10*x^3 - 3*x^2 - 4*x - 8
cover 1 point over quartic algebra = [7/y^2*x^4 + 2/y^2*x^3 + 13/y^2*x^2 + 40/y^2*x - 5/y^2, 17/y^3*x^6 - 17/y^3*x^5 + ((-7*y - 170)/(2*y^3))*x^4 + ((-y - 255)/y^3)*x^3 + ((-13*y + 85)/(2*y^3))*x^2 + ((-40*y - 119)/(2*y^3))*x + ((-y^3 + 5*y - 170)/(2*y^3))]
cover 1 rational points searched = [[3/2, 17/4], [3/2, -17/4]]
17 phi q[1] points = [[0, 17], [0, -17]]
17 phi q[17] points = [[-1, 8], [-1, -8], [1, 8], [1, -8]]
17 phi q[-1] points = []
17 phi q[-17] points = []
17 dual q[1] points = [[-8, 0], [8, 0]]
17 dual q[-1] points = [[-2, 0], [0, 16], [0, -16], [2, 0]]
17 dual q[2] points = []
17 dual q[-2] points = []
[0;31m[0;31m  ***   syntax error, unexpected end of file, expecting )-> or ',' or ')': 
[0;31m  ***   [0;35mfor(U=0,511[0;35m,
[0;31m[0;31m  ***              ^-[0m
[0;31m[0;31m  ***   syntax error, unexpected end of file, expecting )-> or ',' or ')': 
[0;31m  ***   [0;35mfor(V=0,511[0;35m,
[0;31m[0;31m  ***              ^-[0m
[0;31m[0;31m  ***   syntax error, unexpected end of file, expecting )-> or ',' or ')': 
[0;31m  ***   [0;35mif((U%2)||(V%2)[0;35m,
[0;31m[0;31m  ***                  ^-[0m
[0;31m[0;31m  ***   syntax error, unexpected ')', expecting end of file:[0;35m );
[0;31m[0;31m  ***                                                        ^--[0m
[0;31m[0;31m  ***   syntax error, unexpected ')', expecting end of file:[0;35m );
[0;31m[0;31m  ***                                                        ^--[0m
[0;31m[0;31m  ***   syntax error, unexpected ')', expecting end of file:[0;35m );
[0;31m[0;31m  ***                                                        ^--[0m
primitive residue pairs mod 512 for dual d=2 = 0
primitive residue pairs mod 512 for dual d=-2 = 0
analytic rank = [0, 0.38676993838778004330239475124323592948]
L1 = 0.38676993838778004330239475124323592948
bsd = 0.38676993838778004330239475124323592948
periods = [-0.77353987677556008660478950248647185896 + 1.3728695590448768360170939401900545357*I, 1.5470797535511201732095790049729437179]
tamagawa = 4
modular degree = 1
=== 19a1 ===
disc = -6859
j = -89915392/6859
tors = [3, [3], [[5, 9]]]
rank = [0, 0, 0, []]
#ell2cover = 0
ell2cover raw = []
19 quartic A factorization = [x - 2, 1; x^3 + 3*x^2 + x - 3, 1]
19 quartic B factorization = [3*x - 2, 1; x^3 + 2*x^2 - 4, 1]
19 quartic C factorization = [x - 1, 1; 3*x^3 - 2*x^2 - 12*x - 8, 1]
19 quartic A points = [[1, 2], [1, -2], [2, 0]]
19 quartic B points = [[1, 1], [1, -1], [2/3, 0]]
19 quartic C points = [[1, 0], [2, 4], [2, -4]]
analytic rank = [0, 0.45325324449610360357883918706484630905]
L1 = 0.45325324449610360357883918706484630905
bsd = 0.45325324449610360357883918706484630905
periods = [0.67987986674415540536825878059726946357 + 2.0635461958586202323379156581609523042*I, 1.3597597334883108107365175611945389271]
tamagawa = 3
modular degree = 1
```

## mwrank 17a1, verbosity 5, Selmer-only
```text
Program mwrank: uses 2-descent (via 2-isogeny if possible) to
determine the rank of an elliptic curve E over Q, and list a
set of points that generate E(Q) modulo 2E(Q).
and finally saturate to obtain generating points on the curve.
For more details see the mwrank documentation.
For details of algorithms see the author's book.

Please acknowledge use of this program in published work, 
and send problems to john.cremona@gmail.com.

eclib version 20231211, using NTL bigints and NTL real and complex multiprecision floating point
Using multiprecision floating point with 50 bits precision.
Enter curve: Curve [1,-1,1,-1,-14] :	
1 points of order 2:
[22:-15:8]

(c,d)  =(30,289)
(c',d')=(-60,-256)
Using 2-isogenous curve [0,-60,0,-256,0] (minimal model [1,-1,1,-6,-4])
-------------------------------------------------------
First step, determining 1st descent Selmer groups
-------------------------------------------------------
Finding els gens for E (c= 30, d= 289)
Support (length 2): [ -1 17 ]
Adding (torsion) els generator #1: d1 = 17
After els sieving, nelsgens = 1
2-rank of S^{phi}(E') = 1
(els)gens: [ 17 ]

Finding els gens for E' (c'= -60, d'= -256)
Support (length 2): [ -1 2 ]
Adding (torsion) els generator #1: d1 = -1
After els sieving, nelsgens = 1
2-rank of S^{phi'}(E) = 1
(els)gens: [ -1 ]
After first local descent, rank bound = 0
rk(S^{phi}(E'))=	1
rk(S^{phi'}(E))=	1

-------------------------------------------------------
Second step, determining 2nd descent Selmer groups
-------------------------------------------------------
...skipping since we already know rank=0
After second local descent, rank bound = 0
rk(phi'(S^{2}(E)))=	1
rk(phi(S^{2}(E')))=	1
rk(S^{2}(E))=	1
rk(S^{2}(E'))=	2

selmer-rank = 1
upper bound on rank = 0
Enter curve: 
```

## mwrank 19a1, verbosity 5, Selmer-only
```text
Program mwrank: uses 2-descent (via 2-isogeny if possible) to
determine the rank of an elliptic curve E over Q, and list a
set of points that generate E(Q) modulo 2E(Q).
and finally saturate to obtain generating points on the curve.
For more details see the mwrank documentation.
For details of algorithms see the author's book.

Please acknowledge use of this program in published work, 
and send problems to john.cremona@gmail.com.

eclib version 20231211, using NTL bigints and NTL real and complex multiprecision floating point
Using multiprecision floating point with 50 bits precision.
Enter curve: Curve [0,1,1,-9,-15] :	Using (a,b,c) search with (a,h) sieve and algebraic method
(with bigints to solve the syzygy)
Basic pair: I=448, J=20176
disc=-47409408
2-adic index bound = 2
By Lemma 5.1(a), 2-adic index = 1
2-adic index = 1
One (I,J) pair
(a,h) sieving using 12 moduli: 
p:	9	13	23	29	31	37	41	53	59	67	71	79	
k_p:		1	2	1	1	1	1	1	1	1	1	1	
phi1:		0	6	13	25	1	7	23	55	6	25	49	
phi2:		*	8	*	*	*	*	*	*	*	*	*	
phi3:		*	-14	*	*	*	*	*	*	*	*	*	
finished aux_init()
Before sorting, phi = (21.31481749245,-4.3548058750415),(21.31481749245,4.3548058750415),(-42.629634984899,0)
starting flag_init()
finished flag_init()
Looking for quartics with I = 448, J = 20176
Looking for Type 3 quartics:
After  sorting, phi = (21.31481749245,-4.3548058750415),(21.31481749245,4.3548058750415),(-42.629634984899,0)
Basic a bound = 7.605263819371
Search range for a: (-7,0)
Search range for a: (-7,0)
Trying negative a from -1 down to -7
(-2,-2,10,10,-12)	(ipivot = -1, type = A) 	(0:00:0:0:0:0:0:0:0:0:0)	--trivial
(-3,-4,4,12,-8)	(ipivot = -1, type = A) 	(0:00:0:0:0:0:0:0:0:0:0)	--trivial
(-3,5,10,-4,-8)	(ipivot = -1, type = A) 	(0:00:0:0:0:0:0:0:0:0:0)	--trivial
Finished looking for Type 3 quartics.
288	 (a,b,c) triples in search region
80	 failed c-divisiblity,
201	 failed syzygy sieve,
7	 passed sieve.
0	 failed syzygy after sieving,
5	 failed d-integrality,
3	 failed e-integrality,
0	 failed extra-2 divisibility conditions,
3	 passed all and produced quartics.
After getquartics(): 
n1 = 1
n2 = 1
n3 = 0
B-rank = 0
Selmer  rank contribution from B=im(eps) = 0
Selmer  rank contribution from A=ker(eps) = 0
Selmer rank = 0
selmer-rank = 0
upper bound on rank = 0
Enter curve: 
```
