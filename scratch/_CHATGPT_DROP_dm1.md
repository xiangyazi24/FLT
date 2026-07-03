# Q3166 (dm1): Paper 2 counterexample research — keyWeight boundary mechanism

Date: 2026-07-03

## Executive answer

The cleanest way to understand the counterexample is this:

```text
The tau pairing cancels the bilateral/bulk kernel.
The failure is entirely a boundary flux through one-sided cuts.
Those boundary cuts are q^9-dilated because the root-pair row coefficient is

    n(l) = 54l + 45 = 9(6l+5).

Therefore nonzero keyWeight is impossible away from e ≡ 0 mod 9.
```

But I would be careful with the phrase “fails iff 9|e.”  The data quoted says all failures occur at multiples of 9, but many multiples of 9 still have no failure.  The theorem you should aim to prove is:

```text
Eligibility theorem:
  if 9 ∤ e, every fiber is tau-closed and keyWeight(e,K)=0.

Boundary theorem:
  if 9 | e, keyWeight(e,K) is a signed boundary representation number.
  It may vanish by cancellation or by no boundary representative.
```

So `9|e` is a necessary support condition for the residual, not by itself a sufficient condition for each fiber.

The sigma involution on the `(k,r)` cone is the right repair.  The corrected local statement should not be “tau closes every fiber,” but:

```text
keyWeight(e,K) is the divergence of a tau/sigma boundary current.
It vanishes exactly when the fiber has no sigma-straddling boundary atoms,
or when their signed boundary count cancels.
```

This recovers a fiber-local proof after adding boundary edges or ghosts.  The quotient proof should pair atoms in the enlarged graph, not in the original support alone.

## Repo context used

I checked the current Q-series repo notes.  The active Chapter 10 route emphasizes the faithful bridge through `Fhm = Ghat 1`, specialization at `(18,18,1)`, and the importance of boundary clearing before specialization.  The run log also records the key specialization denominator shape `Wd(r)=90r-D_row`, with `|Wd| ≥ 9` at `(18,18)`.  That is consistent with the answer below: the residual is not a random failure of tau; it is a q^9/q^18 boundary phenomenon coming from the specialized row arithmetic.

## 1. Why the `9 | e` condition appears

### 1.1 The short mechanism

The noncentral tau cancellation fails only when the atom lies on a one-sided boundary.  The boundary terms come from row equations in which the root-pair linear coefficient is

```text
n(l) = 54l + 45 = 9(6l+5).
```

Equivalently, with `m=l+1`,

```text
n = 54m - 9 = 9(6m-1).
```

Under tau, `m -> -m`, so

```text
n_tau = -54m - 9 = -n - 18.
```

After dividing by 9, if

```text
a = n/9 = 6m - 1,
```

then tau sends

```text
a -> -a - 2.
```

So the tau root-pair symmetry is an affine reflection centered at `a=-1`, but only after the coefficient has been divided by 9.  This is the first structural reason the residual lives on a 9-dilated lattice.

### 1.2 Boundary energies are images of a 9-dilated quadratic

The general pattern is:

```text
bulk row contribution       = bilateral theta / complete root-pair orbit,
boundary row contribution   = one-sided or strip-truncated root-pair orbit.
```

For a typical root variable `j`, the row equation has schematic form

```text
e = A j^2 + n(l) j + C(other variables),
```

where the boundary part is obtained by restricting `j` to one side of a cut.  Since `n(l)=9(6l+5)`, completing the square or performing the root-pair involution shows that the boundary polynomial is naturally expressed as

```text
e = 9 * R(boundary variables),
```

possibly after the fixed row normalization used by the Chapter 10 dissection.

This is exactly what the Paper 3 cone factor sees:

```text
Missing_kernel = Theta_u * Theta_v * (D - A),
```

where the cone factor is a discriminant-5 Hecke-type false/indefinite theta series.  In the even-row normalization, the cone exponent is usually written as `9E` or `18N`; in other parity/coset components the same mechanism can produce `9` rather than `18`.  This explains why `90`, `702`, and `11763` are all multiples of `9`, while not necessarily all multiples of `18`.

### 1.3 What needs to be proved

The right theorem is not simply “because `n` is divisible by 9.”  The proof should factor the boundary contribution.

A precise target theorem is:

```text
BoundarySupportTheorem.
For every fiber K and exponent e,

  keyWeight(e,K) = BoundaryWeight(e,K),

where BoundaryWeight(e,K) is a finite signed sum over boundary variables and
is supported only when e = 9E_boundary for some integer E_boundary.

Consequently, if 9 ∤ e, then keyWeight(e,K)=0.
```

This is stronger and cleaner than checking tau support directly.

### 1.4 Why some multiples of 9 pass

The quoted data says:

```text
non-9-multiples: no failures;
9-multiples: many failures, but not all.
```

That is exactly what a boundary representation theorem predicts.  Multiples of 9 are eligible, but a particular fiber may still have no boundary representative or may have signed cancellation.  In Paper 3 language, this is the same distinction as:

```text
norm-eligible does not imply nonzero coefficient.
```

The correct statement should be:

```text
keyWeight can fail only on the q^9 boundary subseries.
```

not:

```text
every multiple of 9 fails.
```

## 2. keyWeight as a boundary divergence

Yes.  This is the right repair.

Let `A_e` be the set of atoms at exponent `e`, let `χ_e(x)` be the support indicator, and let `τ` be the central reflection in `(m,t)`:

```text
τ(m,t,d) = (-m,-t,d).
```

Let `s(x)` be the outer sign, with

```text
s(τx) = -s(x)
```

for noncentral atoms.  Then, for a fixed fiber `K`, the tau-paired keyWeight can be written as

```text
keyWeight(e,K)
  = 1/2 * sum_{x in K-orbit domain}
        s(x) * (χ_e(x) - χ_e(τx)) * localWeight(x).
```

The bulk bilateral piece has

```text
χ_e(x) = χ_e(τx)
```

and cancels.  Thus only the support-boundary term survives:

```text
boundaryFlux_e(x)
  = s(x) * (χ_e(x) C_boundary(x) - χ_e(τx) C_boundary(τx)).
```

This is a discrete divergence.  More invariantly, make a graph whose vertices are atoms and whose edges connect `x` to `τx`.  Define a current on each edge by the signed contribution transported from one endpoint to the other.  Then keyWeight is the divergence of this current restricted to the cut support.

### 2.1 Boundary edge family

The concrete boundary edge families are:

```text
1. missing-half theta edges;
2. U-strip edges;
3. V-strip edges;
4. the k,r Hecke-Rogers cone wall D-A.
```

The sigma involution

```text
sigma(k,r) = (k, -r - 6k - 1)
```

preserves the `(k,r)` quadratic energy and flips the sign `(-1)^r`.  Hence the full bilateral `(k,r)` sum cancels, and the residual is exactly a cone-wall difference.

That gives the repaired theorem:

```text
CorrectedFiberTheorem.
For a fixed fiber K, keyWeight(e,K)=0 if the fiber is sigma-closed across the
boundary edge family.  Otherwise keyWeight(e,K) equals the signed count of
sigma-straddling boundary atoms in that fiber.
```

This is the right replacement for the failed `keyWeight=0` conjecture.

### 2.2 How this rescues the proof

The original proof tried to pair atoms inside the original support.  The ghost partner at `(4,21,4)` shows that the original support is not tau-closed.  The repaired proof enlarges the object:

```text
original support + ghost boundary edges + sigma reflection data.
```

Then cancellation happens in the enlarged graph, and the obstruction is pushed to a boundary divergence term.  If the global q-series identity includes the corresponding boundary correction, the proof closes.

## 3. Does the ghost partner re-enter support by a deck transformation?

Probably yes, but not by tau alone and not by a simple translation in `(m,t,d)`.

There are three relevant deck phenomena.

### 3.1 Root-row affine deck

In the normalized row coefficient

```text
a = n/9 = 6m - 1,
```

tau acts by

```text
a -> -a - 2.
```

For the counterexample

```text
m = -4,
a = 6(-4)-1 = -25,
a_tau = 23 = -(-25)-2.
```

Thus the ghost is visible in the affine root-pair quotient whose reflection center is `a=-1`.  This suggests a deck action in the root-row variable with affine shift `2` after dividing by 9.

### 3.2 Cone deck via sigma

On the Hecke-Rogers cone side, the relevant deck/reflection is not tau but

```text
sigma(k,r) = (k, -r - 6k - 1).
```

It preserves the quadratic energy and reverses the parity sign.  The ghost partner should therefore be interpreted as re-entering after applying the sigma wall reflection in the boundary cone.  In the quotient by the sigma pairing, the bilateral sum is zero.

### 3.3 Ideal/coset deck via the unit stabilizer

On the Paper 3 norm side, the natural deck group is

```text
Gamma = <eps^6>,
```

because `eps^6 L = L`.  The period `6` is a multiplicative unit-sector period; it is not the same as the additive q-exponent period `9`, but both carry a mod-3 component.

### 3.4 What period to test

I would test three candidate periods separately:

```text
q-exponent period:      9,
root-row affine period: a -> -a-2 in a=n/9,
unit/coset period:      eps^6.
```

For the ghost atom, do not expect a literal `(m,t,d) -> (m+P,t+Q,d)` translation to fix the support.  The support is cut by half-open strips and cone walls, so the natural deck is an affine reflection plus unit-sector reduction, not a rectangular lattice period.

A good diagnostic is:

```text
Given a ghost y=τx outside support, search for g in <sigma, eps^6> or in the
root-row affine deck group such that g(y) lies in the same energy/fiber support.
```

If this succeeds uniformly, the quotient proof should be formulated over that deck group.

## 4. Shape of the support set in `(m,t,d)`

Use

```text
m = l + 1,
t = u + v - 1,
d = u - v,
```

so

```text
u = U = (t + d + 1)/2,
v = V = (t - d + 1)/2,
l = m - 1.
```

The integrality/parity condition is:

```text
t + d + 1 is even,
t - d + 1 is even.
```

Equivalently, `t+d` and `t-d` are odd, so `t` and `d` have opposite parity.

### 4.1 Strip support intervals

The uniform strip function is

```text
strip0(N,l) = H(l) - H(l-N),
```

where `H(x)=1` for `x>=0` and `0` otherwise.  In `m`-coordinates:

```text
strip0(N,m-1) = H(m-1) - H(m-1-N).
```

Equivalently define the half-open interval

```text
I(N) =
  { m : 1 <= m <= N }       if N > 0,
  { m : N+1 <= m <= 0 }     if N < 0,
  empty                     if N = 0.
```

Then

```text
U-strip support:  m in I(U),
V-strip support:  m in I(V).
```

Under tau,

```text
m -> -m,
t -> -t,
d -> d,
U -> 1 - V,
V -> 1 - U.
```

So the tau-reflected U-strip condition is

```text
-m in I(1 - V),
```

and the tau-reflected V-strip condition is

```text
-m in I(1 - U).
```

These are not equal to the original conditions in general.

### 4.2 Explicit strip defects

The U-strip tau defect is

```text
∂τ S_U(m,t,d)
  = strip0(U, m-1) - strip0(1-V, -m-1)
  = H(m-1) - H(m-1-U) - H(-m-1) + H(V-m-2).
```

The V-strip tau defect is

```text
∂τ S_V(m,t,d)
  = strip0(V, m-1) - strip0(1-U, -m-1)
  = H(m-1) - H(m-1-V) - H(-m-1) + H(U-m-2).
```

Those two formulas are the explicit support-boundary equations in `(m,t,d)` for the strip pieces.

### 4.3 Missing-half support

The missing-half piece should be expressed in the root variable whose row coefficient is

```text
n = 9(6m-1).
```

Its generic shape is a one-sided inequality such as

```text
j >= 0
```

paired with a root-pair transformation of the form

```text
j -> -j - A(m, other data),
```

where the affine parameter is divisible by the normalized row coefficient.  The exact support set is therefore:

```text
S_e(K)
  = energy equation at exponent e
    ∩ parity/integrality conditions in (m,t,d)
    ∩ root-packet inequalities
    ∩ one-sided missing-half or strip conditions.
```

The important point is that `S` is not a single convex tau-invariant region.  It is a finite union of half-open polyhedral regions, and tau moves the anchors `m=0,1` and swaps `U,V` affinely.

### 4.4 The counterexample in these coordinates

For the atom

```text
(m,t,d)=(-4,-21,4),
```

we get

```text
U = (-21 + 4 + 1)/2 = -8,
V = (-21 - 4 + 1)/2 = -12.
```

Tau sends it to

```text
(4,21,4),
U_tau = 1 - V = 13,
V_tau = 1 - U = 9.
```

The support mismatch is therefore not mysterious: the original and reflected points live relative to different half-open strip intervals anchored at `m=0,1`, and the missing-half/root condition lives in a row whose coefficient has been reflected from `9(6m-1)` to `9(-6m-1)`.

## 5. Relationship between `9|e` and the order-6 stabilizer

There is probably a common mod-3 source, but I would not claim a direct theorem yet.

### 5.1 What is definitely true

The `9|e` condition is additive/q-series data:

```text
n(l)=54l+45=9(6l+5),
```

and the boundary exponent is a q^9-dilated representation number.

The order-6 stabilizer is multiplicative/ray-class data:

```text
eps has order 3 mod 2, order 2 mod sqrt(5), so order 6 mod 2sqrt(5),
eps^6 stabilizes L.
```

These are different structures.

### 5.2 The common `3`

The common `3` is likely structural.  The Chapter 10 dissection uses cubic/root-of-unity filtering and q^3/q^9 substitutions.  On the `Q(sqrt(5))` side, the prime `2` is inert and

```text
O_K / 2O_K ≅ F_4,
F_4^× has order 3.
```

Thus both sides contain a natural order-3 sector:

```text
additive side:     q^9 = (q^3)^3, root-packet row coefficient divisible by 9;
multiplicative side: F_4^× order 3, unit-sector invariant iota in Z/3Z.
```

This suggests that the same cubic dissection/filtering that creates the `q^9` boundary subseries also creates the order-3 finite-field sector in Paper 3.

### 5.3 What not to claim

Do not claim:

```text
9|e follows from eps^6 stabilizer.
```

That is too strong and likely false as a direct implication.  The safer statement is:

```text
Both phenomena are shadows of the same cubic/cyclotomic layer of the
Theta_10 dissection: the additive boundary is q^9-dilated, while the
multiplicative norm model has an F_4^× sector of order 3.
```

A possible future theorem would identify both as images of one underlying mod-3 root-of-unity filter.

## 6. Proposed theorem package

I would reorganize the research target into the following theorem package.

### Theorem A: tau-pair decomposition

```text
For every exponent e and fiber K,
keyWeight(e,K) = Bulk(e,K) + Boundary(e,K),
Bulk(e,K)=0 by tau pairing.
```

### Theorem B: q^9 support of boundary

```text
Boundary(e,K)=0 unless 9 | e.
```

Proof route: express the boundary edge families as q^9-dilated quadratic/false-theta sums.

### Theorem C: boundary divergence formula

```text
Boundary(e,K) = div(J_e)(K),
```

where `J_e` is the tau/sigma edge current across missing-half and strip boundaries.

### Theorem D: sigma-straddling criterion

```text
Boundary(e,K) is the signed count of sigma-straddling atoms in the fiber.
If the fiber is sigma-closed, keyWeight(e,K)=0.
```

### Theorem E: cone identification

```text
Global boundary generating function = Theta_u * Theta_v * (D-A),
D-A = -f_{1,3,4}(X,-X^3,X).
```

This connects the local counterexample to Paper 3.

### Theorem F: deck quotient cancellation

```text
After adjoining ghost boundary edges and quotienting by the sigma/deck action,
the lifted keyWeight vanishes.  The original keyWeight is the boundary charge
of the quotient projection.
```

This is the conceptual replacement for the false keyWeight=0 conjecture.

## 7. Lean theorem shapes

Here is the Lean-facing shape I would aim for.  This is only an interface sketch, not code claimed to compile against the existing files.

```lean
import Mathlib.Tactic

namespace QseriesFormalization
namespace Ch10

/-- Abstract atom type for the fiber-level theorem. -/
structure Atom where
  m : Int
  t : Int
  d : Int
  k : Int
  r : Int
  deriving DecidableEq, Repr

/-- Tau reflection in `(m,t)` with fixed `d`; k,r behavior is supplied separately. -/
def tauMTD (x : Atom) : Atom :=
  { x with m := -x.m, t := -x.t }

/-- Hecke-Rogers wall reflection on the `(k,r)` block. -/
def sigmaKR (x : Atom) : Atom :=
  { x with r := -x.r - 6*x.k - 1 }

/-- Boundary eligibility: the q^9 support theorem. -/
def BoundaryEligible (e : Int) : Prop :=
  9 ∣ e

/-- A schematic boundary flux functional. -/
def BoundaryFlux
    (support : Atom -> Prop)
    (sgn : Atom -> Int)
    (weight : Atom -> Int)
    (x : Atom) : Int :=
  if support x then sgn x * weight x else 0
  -- In the real theorem this is paired with the tau/sigma reflected endpoint.

/-- Target theorem shape: no boundary off the q^9 subseries. -/
theorem keyWeight_zero_of_not_nine_dvd
    (keyWeight : Int -> Int -> Int)
    (e key : Int)
    (h : ¬ 9 ∣ e) :
    keyWeight e key = 0 := by
  -- This should follow from the q^9 boundary support theorem, not from brute force.
  admit

end Ch10
end QseriesFormalization
```

The `admit` above is deliberately included only to show theorem shape.  It should not be copied into the no-sorry development.

## 8. Answers to the five questions

### Q1. Why `9|e` precisely?

Because the tau residual is not a bulk term.  It is a boundary term, and the boundary row coefficient is `n=54l+45=9(6l+5)`.  After root-pair reflection/completing-square normalization, the boundary energy is a q^9-dilated quadratic/false-theta representation.  Thus nonzero keyWeight is impossible unless `e` lies in `9Z`.  Multiples of 9 are only eligible; they can still pass by absence or cancellation of boundary representatives.

### Q2. Can residual keyWeight be a boundary divergence?

Yes.  This is the right repair.  Pair the tau orbit in the bulk, then write the uncancelled contribution as

```text
s(x) * (χ(x)C(x) - χ(τx)C(τx)).
```

This is a discrete divergence across the support cut.  The sigma involution identifies the Hecke-Rogers boundary wall, so the residual is a signed count of sigma-straddling atoms.

### Q3. Does the ghost partner re-enter by a deck transformation?

Likely yes in the enlarged quotient, but not by tau alone.  The relevant deck data are: additive q-period `9`, normalized row reflection `a -> -a-2` for `a=n/9`, sigma wall reflection on `(k,r)`, and multiplicative unit stabilizer `<eps^6>` on the norm side.  Do not expect a simple rectangular translation in `(m,t,d)`.

### Q4. What is the support shape in `(m,t,d)`?

It is a finite union of half-open polyhedral pieces.  The strip pieces are explicit:

```text
U = (t+d+1)/2,
V = (t-d+1)/2,
I(N) = [1,N] if N>0, [N+1,0] if N<0, empty if N=0.

U-strip: m in I(U),
V-strip: m in I(V).
```

Tau sends `U -> 1-V`, `V -> 1-U`, and `m -> -m`, so the strip support is not tau-invariant.  The exact strip defects are the Heaviside formulas above.  The missing-half piece should be written similarly in the root variable with row coefficient `9(6m-1)`.

### Q5. Is there a relationship between `9` and order `6`?

Probably, but only through a common mod-3 layer.  The `9` is additive q-series dilation from the root row; the `6` is multiplicative unit/coset stabilization, with order `3` mod `2` and order `2` mod `sqrt(5)`.  The common `3` is likely the cubic-dissection/F_4^× sector.  This is a structural analogy and a promising unification target, not yet a direct implication.

## Bottom line

The counterexample does not mean the Chapter 10 proof idea is dead.  It means the naive support-local tau pairing was missing a boundary term.  The corrected statement should be:

```text
The tau bulk cancels.
The entire obstruction is a q^9-supported boundary divergence.
That divergence is the local fiber shadow of the global Hecke-Rogers cone
D-A = -f_{1,3,4}(X,-X^3,X).
```

This gives a coherent path forward: prove zero off `9Z`, express the `9Z` residual as sigma-straddling boundary flux, and then either add the required boundary correction or pass to the appropriate deck/ghost quotient where the lifted pairing is exact.
