# `X_1(13)` weak 2-descent: reproducible arithmetic inventory

This note records computations for the sextic field used by the standard
fake-2-descent on the genus-two curve

```text
C : y^2 = f(x),
f = x^6 + 4x^5 + 6x^4 + 2x^3 + x^2 + 2x + 1.
L = Q[T]/(f(T)).
```

It is an inventory, not a proof of a Selmer theorem.  Each PARI calculation
below is independently reproducible, but Lean must ultimately prove the
corresponding integral-basis, ideal, and local-solubility statements.

## PARI/GP transcript

The following ran with the repository host's `gp` executable.

```gp
x='x;
f=x^6+4*x^5+6*x^4+2*x^3+x^2+2*x+1;
nf=nfinit(f); b=bnfinit(f);

print(nf.disc); print(nf.index); print(nf.zk);
print(b.no); print(b.cyc); print(b.fu); print(b.tu);
print(idealprimedec(nf,2)); print(idealprimedec(nf,13));
print(factor(Mod(1,2)*f)); print(factor(Mod(1,13)*f));
print(polgalois(f)); print(nf.sign);
```

Output:

```text
nf.disc = -10816 = -2^6 * 13^2
nf.index = 8
nf.zk = [
  1,
  (T^5+3T^4+3T^3+3T)/2,
  (-T^5-3T^4-2T^3+4T^2-1)/2,
  (T^5+4T^4+6T^3+3T^2+3T+3)/2,
  (-2T^5-7T^4-9T^3-T^2-2T-1)/2,
  T^5+7T^4/2+4T^3-T^2/2+T/2+1
]

class number = 1; class-group invariants = []
fundamental units = [
  e1=(-T^5-3T^4-3T^3-3T)/2,
  e2=(-T^5-3T^4-2T^3+4T^2-1)/2
]
torsion units = [4, zeta],
  zeta=T^5+7T^4/2+9T^3/2+T^2/2+2T+3/2.

signature = [0,3]
Galois group reported by polgalois = [18,-1,1,"F_18(6) = [3^2]2 = 3 wr 2"]
```

Thus the unit rank is two and the torsion-unit group has order four.  The
integral basis, rather than the power basis, is essential at `2`: the power
basis has index `8`.

## Bad primes and principal generators

The same script, augmented by `bnfisprincipal(b, P, 1)`, gives the following
principal generators (written in the power basis only for readability):

```text
a2 = T^5 + 7T^4/2 + 9T^3/2 + T^2/2 + 2T + 1/2,       Norm(a2)=8
a  = (-T^3 - 2T^2 - T + 3)/2,                         Norm(a)=13
q  = -3T^5 - 21T^4/2 - 27T^3/2 - 3T^2/2 - 6T - 5/2, Norm(q)=13^3
```

`idealprimedec` returns:

```text
(2)  = P2^2,              e(P2/2)=2, f(P2/2)=3,
(13) = P^3 Q,             e(P/13)=3,  f(P/13)=1,
                            e(Q/13)=1,  f(Q/13)=3,
(a2)=P2, (a)=P, (q)=Q.
```

For `13` the factorization can also be checked directly modulo `13`:

```text
f = (T+4)^3 * (T^3+5T^2+2T+12) mod 13.
```

Modulo `2` it is

```text
f = (T^3+T+1)^2 mod 2.
```

The latter does **not** by itself prove the prime-ideal statement because
the power-basis index is divisible by `2`; it is only a consistency check for
the `idealprimedec` result.

PARI's `bnfisunit` additionally gave the exact unit-coordinate checks

```text
a2^2 / 2       has unit coordinates [0,0,3],
13 / (a^3*q)  has unit coordinates [2,1,2].
```

Here PARI orders the coordinates as `[e1,e2,zeta]`.  Direct reduction modulo
`f` independently checked the interpretation.  Consequently the
following two identities are the useful Lean targets (after fixing the
integral basis and unit notation):

```text
a2^2 = 2 * zeta^3,
13   = zeta^2 * e1^2 * e2 * a^3 * q.
```

They are finite polynomial reductions modulo `f`; they should be verified in
Lean by clearing the displayed halves and `ring_nf`, not imported as PARI
facts.

For reproducibility, the generator calculation was:

```gp
S=concat(idealprimedec(nf,2),idealprimedec(nf,13));
print(bnfsunit(b,S)[1]);
```

It returns `[a2,a,q]`; its S-class group is `[1,[],[]]`.

## Candidate envelope before local conditions

A standard fake-2-descent class lies in a squareclass group in `L^*/L^{*2}`
with a rational norm constraint.  From the preceding *global* ideal data,
every class unramified outside `S={2,13}` is represented, modulo squares, by

```text
zeta^i * e1^j * e2^k * a2^r * a^s * q^t,
i,j,k,r,s,t in {0,1}.
```

The necessary condition that its rational norm be a square imposes

```text
r = 0 mod 2,
s+t = 0 mod 2.
```

Therefore this norm-compatible S-unit envelope has only `2^4=16` classes;
one may take representatives

```text
zeta^i * e1^j * e2^k * (a*q)^s,  i,j,k,s in {0,1}.
```

This is **not yet** a fake Selmer computation.  It only uses class number,
S-units, and the necessary norm condition.  The actual fake Selmer condition
requires the relevant two-covering to have points over `Q_v` at every place.
PARI/GP has no command here that proves those genus-two local-solubility
claims, so no local elimination has been asserted in this note.

The expected final answer is the trivial fake-Selmer class: the published
arithmetic is `J_1(13)(Q) = Z/19Z`, hence `J(Q)/2J(Q)=0`.  That expectation
must not be used backwards to discard any of the 16 classes.

## Existing exact geometry that makes the descent structural

The repository now proves, in
`FLT/Assumptions/MazurProof/N13DiamondQuotient.lean`, the rational order-three
diamond quotient:

```text
u = (x^3-3x-1)/(x(x+1)),
z = y/(x(x+1)),
z^2 = u^2+4u+8,
x^3-u*x^2-(u+3)*x-1 = 0.
```

The conic has the rational parametrization

```text
u = t^-1-t-2,    z = t+t^-1,
t = (z-u-2)/2.
```

This explains why the order-three quotient is genus zero but does not prove
the six-cusp theorem: its fibers are cubic.  The descent target remains the
genus-two Jacobian, not the conic alone.

## Minimal Lean certificate boundary

The next honest formal interface should consist of finite, independently
checkable fields rather than a broad rank axiom:

1. an integral-basis certificate for the six displayed basis elements;
2. polynomial norm identities for `e1,e2,zeta,a2,a,q`;
3. ideal-factorization certificates at `2` and `13`;
4. a 16-row local-image certificate for the actual fake-2 covering, with
   explicit residue/completion witnesses or contradictions;
5. a group-theoretic deduction that the surviving image is trivial.

Items 1--3 are algebraic and can be introduced incrementally.  Item 4 is the
only genuine fixed-instance arithmetic block still missing.
