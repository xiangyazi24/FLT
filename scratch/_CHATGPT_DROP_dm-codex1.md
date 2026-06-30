# Q2719 (dm-codex1): divided-by-3 square branch audit

Repo/branch requested: `xiangyazi24/FLT@scratch`  
Lean project context: `flt-ai`  
Target local frontier: `FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean`  
Namespace expected from prior drops: `MazurProof.RationalPointsN12`

Connector note: the remote `scratch` branch is writable. The local WIP Lean file named in the prompt was not visible through the connector, so this audit is based on the exact definitions supplied in the prompt.

## Executive verdict

The divided branch is not the raw branch with a harmless factor of `3` stripped off. The forced nonsquare factor `3` in

```text
3*A^2 = (m-n)*(m+n)
3*N^2 = n*(2*m-n)
```

goes respectively into `m+n` and `2*m-n`. In fact `3 ∣ (2*m-n)` is forced.

After the honest gcd/valuation split there are three parity packages. Two die immediately modulo `4`; the only survivor is the `m` even, `n` odd package, and it yields four positive squares in arithmetic progression:

```text
c^2, b^2, d^2, a^2.
```

So the remaining residual is not the raw-package `EulerSquarePair` directly. The Lean-friendly route is:

```text
DividedSquareBranch
  → gcd/valuation table
  → three factor packages
  → mod-4 contradiction for the n-even package
  → mod-4 contradiction for the both-odd package
  → FourSquaresAP c b d a in the m-even/n-odd package
  → unit (A,N,S)=(1,1,1), assuming no nonconstant four-square AP
  → close DividedSquareBranchUnitOrDescendsStatement by Or.inl.
```

With the current `PositivePrimitiveEisensteinBadUnordered`, the unit case is itself excluded by `A^2 ≠ N^2`; nevertheless it is exactly the explicit unit exception in the target statement.

## 1. Gcds and valuations

Write

```text
x = m - n,
y = m + n,
z = n,
w = 2*m - n.
```

From `0 < n` and `n < m`, all four are positive. From `IsCoprime m n`:

```text
gcd(x,z) = gcd(m-n,n)       = 1,
gcd(y,z) = gcd(m+n,n)       = 1,
gcd(x,w) = gcd(m-n,2*m-n)   = 1.
```

The same-equation gcds are:

```text
gcd(x,y) ∣ 2,
gcd(z,w) = gcd(n,2).
```

More exactly:

```text
if m,n have opposite parity, then gcd(x,y)=1;
if m,n are both odd,       then gcd(x,y)=2;
if n is odd,               then gcd(z,w)=1;
if n is even,              then gcd(z,w)=2.
```

The divided-branch cross gcd is exact:

```text
gcd(y,w) = gcd(m+n,2*m-n) = 3.
```

Reason: a common divisor of `y` and `w` divides

```text
y + w   = 3*m,
2*y - w = 3*n.
```

Away from `3`, it would divide both `m` and `n`. Since `3 ∣ y` by hypothesis and

```text
w = 2*m - n = 2*(m+n) - 3*n,
```

we also have `3 ∣ w`, so the common gcd is exactly `3`.

The 3-adic facts are:

```text
3 ∤ n,
3 ∤ m,
3 ∤ (m-n),
3 ∣ (m+n),
3 ∣ (2*m-n),
gcd((m+n)/3, (2*m-n)/3) = 1.
```

The square equations add:

```text
v_3(m+n)    = 1 + 2*v_3(A),
v_3(2*m-n) = 1 + 2*v_3(N),
min(v_3(m+n), v_3(2*m-n)) = 1.
```

So the *nonsquare* factor `3` in `3*A^2` goes to `m+n`, and the nonsquare factor `3` in `3*N^2` goes to `2*m-n`. This does not mean that the exact 3-adic valuation of either factor is always `1`; extra powers of `3` may occur as part of the square.

## 2. Direct answers about divisibility by `3`

`3 ∣ m+n` plus `IsCoprime m n` forces:

```text
3 ∤ n,
3 ∤ m,
3 ∤ (m-n),
3 ∣ (2*m-n).
```

Thus:

* `3∤n` is true.
* `3∤(2*m-n)` is false; the opposite is forced.
* `3∣(m-n)` is false; the opposite is forced.

A minimal counterexample to the tempting false statement `3∤(2*m-n)` is

```text
m = 2, n = 1:
  IsCoprime m n,
  3 ∣ m+n = 3,
  3 ∣ 2*m-n = 3,
  3 ∤ m-n = 1.
```

With `A=N=S=1`, this is also the unit divided branch:

```text
3*A^2 = (m-n)*(m+n) = 1*3,
3*N^2 = n*(2*m-n)   = 1*3,
3*S   = m^2-m*n+n^2 = 3.
```

It is excluded by `PositivePrimitiveEisensteinBadUnordered` because that hypothesis contains `A^2 ≠ N^2`.

## 3. Denominator-free normalization

Because `3 ∣ m+n` and `3 ∣ 2*m-n`, define `p,q` by

```text
m+n    = 3*p,
2*m-n  = 3*q.
```

Then

```text
m = p + q,
n = 2*p - q,
m-n = 2*q - p,
S = p^2 - p*q + q^2,
A^2 = p*(2*q-p),
N^2 = q*(2*p-q),
IsCoprime p q,
0 < p,
0 < q,
0 < 2*q-p,
0 < 2*p-q.
```

This is often the cleanest Lean normalization because it removes literal division by `3`. But it is not the raw branch. The raw branch has

```text
A^2 = (r-s)*(r+s),
N^2 = s*(2*r-s),
```

while the normalized divided branch has the crossed form

```text
A^2 = p*(2*q-p),
N^2 = q*(2*p-q).
```

No single linear renaming of `p,q` makes both equations raw.

## 4. Honest factorization packages

There are three parity cases, since `m,n` are coprime and cannot both be even.

### Case E: `m` odd, `n` even

Here `m-n` and `m+n` are odd, while `n` and `2*m-n` are even. The honest package is

```text
m - n     = a^2,
m + n     = 3*b^2,
n         = 2*c^2,
2*m - n   = 6*d^2,
A         = a*b,
N         = 2*c*d,
0 < a,b,c,d.
```

The identities analogous to the raw packages are

```text
a^2 + c^2 = 3*d^2,
b^2       = c^2 + d^2.
```

This branch is impossible mod `4`: `a` is odd, so `a^2+c^2` is `1` or `2` mod `4`, while `3*d^2` is `0` or `3` mod `4`.

### Case M: `m` even, `n` odd

All four factors are odd except for the forced `3` in `m+n` and `2*m-n`. The honest package is

```text
m - n     = a^2,
m + n     = 3*b^2,
n         = c^2,
2*m - n   = 3*d^2,
A         = a*b,
N         = c*d,
0 < a,b,c,d.
```

The identities are

```text
a^2 + 2*c^2 = 3*b^2,
2*a^2 + c^2 = 3*d^2.
```

Equivalently,

```text
c^2, b^2, d^2, a^2
```

are four squares in arithmetic progression:

```text
b^2 - c^2 = d^2 - b^2,
d^2 - b^2 = a^2 - d^2.
```

This is the real residual. It does not construct the raw `EulerSquarePair` by the raw even/odd formulas. It needs a `FourSquaresAP` theorem, or a bridge from `FourSquaresAP` to the already checked Euler descent.

The degenerate AP case has common difference zero. Then `a=b=c=d`, so

```text
m = 2*a^2,
n = a^2.
```

`IsCoprime m n` forces `a=1`, hence

```text
m=2, n=1, A=1, N=1, S=1.
```

### Case O: `m` odd, `n` odd

Here `m-n` and `m+n` are even, while `n` and `2*m-n` are odd. The honest package is

```text
m - n     = 2*a^2,
m + n     = 6*b^2,
n         = c^2,
2*m - n   = 3*d^2,
A         = 2*a*b,
N         = c*d,
0 < a,b,c,d.
```

The identities are

```text
a^2 + c^2 = 3*b^2,
a^2 + b^2 = d^2.
```

This branch is impossible mod `4`: `c` is odd, so `a^2+c^2` is `1` or `2` mod `4`, while `3*b^2` is `0` or `3` mod `4`.

## 5. Strategic classification

The divided branch is not impossible by a one-line modular obstruction: the middle parity branch survives all small congruence checks and contains the unit example `m=2,n=1,A=N=S=1`.

It is also not reducible to the raw branch by rescaling. The substitution by `p,q` is useful, but it produces crossed equations.

The honest residual is the four-square arithmetic progression in Case M. Therefore the recommended route is:

```text
factorization
  + mod-4 elimination of Case E and Case O
  + NoNonconstantFourSquaresAP for Case M
  ⇒ unit.
```

If the local development already has an Euler descent theorem strong enough to imply no nonconstant four-square AP, prove a bridge theorem. Otherwise, introduce `FourSquaresAP` as the new residual. Avoid `A±N` shortcuts; the branch controls the four linear forms in `m,n`, not factors of `A+N` or `A-N`.

## 6. Lean-friendly Prop definitions and theorem targets

These are intended as minimal intermediate targets. The package definitions include `A` and `N` signs, so the final unit theorem does not redo square-root sign bookkeeping. The positivity of `A,N` comes from `PositivePrimitiveEisensteinBadUnordered`.

```lean
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

namespace MazurProof.RationalPointsN12

/-- Four positive squares in arithmetic progression, written without division. -/
def FourSquaresAP (r s t u : ℤ) : Prop :=
  s ^ 2 - r ^ 2 = t ^ 2 - s ^ 2 ∧
  t ^ 2 - s ^ 2 = u ^ 2 - t ^ 2

/-- Fermat/Euler residual needed for the divided-by-3 branch. -/
def NoNonconstantFourSquaresAP : Prop :=
  ∀ {r s t u : ℤ},
    0 < r → 0 < s → 0 < t → 0 < u →
    FourSquaresAP r s t u →
    r = s ∧ s = t ∧ t = u

/-- Denominator-free form obtained from `m+n=3*p` and `2*m-n=3*q`. -/
def DividedReducedBranch (A N S p q : ℤ) : Prop :=
  0 < p ∧ 0 < q ∧ 0 < 2 * q - p ∧ 0 < 2 * p - q ∧
  IsCoprime p q ∧
  A ^ 2 = p * (2 * q - p) ∧
  N ^ 2 = q * (2 * p - q) ∧
  S = p ^ 2 - p * q + q ^ 2

/-- Target: remove the explicit factor `3`; this is not the raw branch. -/
theorem dividedSquareBranch_to_reduced_target
    {A N S m n : ℤ}
    (h : DividedSquareBranch A N S m n) :
    ∃ p q : ℤ,
      m + n = 3 * p ∧
      2 * m - n = 3 * q ∧
      DividedReducedBranch A N S p q := by
  -- Prove `3 ∣ 2*m-n` from `2*m-n = 2*(m+n)-3*n`.
  -- Then use the two quotients existentially.
  -- `IsCoprime p q` follows from `gcd(m+n,2*m-n)=3`.
  -- The equations follow by cancellation of `3`.
  sorry

/-- Package for the `m` odd, `n` even parity branch. This branch is impossible. -/
def DividedNEvenPackage (A N m n a b c d : ℤ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
  Odd m ∧ Even n ∧
  m - n = a ^ 2 ∧
  m + n = 3 * b ^ 2 ∧
  n = 2 * c ^ 2 ∧
  2 * m - n = 6 * d ^ 2 ∧
  A = a * b ∧
  N = 2 * c * d

/-- Package for the `m` even, `n` odd parity branch. This is the only survivor. -/
def DividedMEvenPackage (A N m n a b c d : ℤ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
  Even m ∧ Odd n ∧
  m - n = a ^ 2 ∧
  m + n = 3 * b ^ 2 ∧
  n = c ^ 2 ∧
  2 * m - n = 3 * d ^ 2 ∧
  A = a * b ∧
  N = c * d

/-- Package for the `m,n` both odd parity branch. This branch is impossible. -/
def DividedBothOddPackage (A N m n a b c d : ℤ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
  Odd m ∧ Odd n ∧
  m - n = 2 * a ^ 2 ∧
  m + n = 6 * b ^ 2 ∧
  n = c ^ 2 ∧
  2 * m - n = 3 * d ^ 2 ∧
  A = 2 * a * b ∧
  N = c * d

/-- Honest factorization split forced by gcd, parity, and the two square equations. -/
def DividedSquareBranchFactorizationStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    DividedSquareBranch A N S m n →
      (∃ a b c d : ℤ, DividedNEvenPackage A N m n a b c d) ∨
      (∃ a b c d : ℤ, DividedMEvenPackage A N m n a b c d) ∨
      (∃ a b c d : ℤ, DividedBothOddPackage A N m n a b c d)

/-- Algebra from the `n` even package. -/
theorem dividedNEvenPackage_identities_target
    {A N m n a b c d : ℤ}
    (h : DividedNEvenPackage A N m n a b c d) :
    a ^ 2 + c ^ 2 = 3 * d ^ 2 ∧
    b ^ 2 = c ^ 2 + d ^ 2 := by
  -- Use `2*m-n = 2*(m-n)+n`, then `m+n = (m-n)+2*n`.
  ring_nf at *
  sorry

/-- The `n` even package is impossible by mod 4. -/
theorem dividedNEvenPackage_false_target
    {A N m n a b c d : ℤ}
    (h : DividedNEvenPackage A N m n a b c d) :
    False := by
  -- From `Odd m`, `Even n`, and `m-n=a^2`, get `Odd a`.
  -- From the identity, get `a^2 + c^2 = 3*d^2`.
  -- Mod 4: odd square plus any square is 1 or 2, but 3*d^2 is 0 or 3.
  sorry

/-- Algebra from the surviving `m` even package: four squares in AP. -/
theorem dividedMEvenPackage_to_fourSquaresAP_target
    {A N m n a b c d : ℤ}
    (h : DividedMEvenPackage A N m n a b c d) :
    FourSquaresAP c b d a := by
  -- From `m-n=a^2` and `n=c^2`, get `m=a^2+c^2`.
  -- Then `m+n=3*b^2` gives `a^2 + 2*c^2 = 3*b^2`.
  -- And `2*m-n=3*d^2` gives `2*a^2 + c^2 = 3*d^2`.
  -- These two identities are exactly the AP equalities.
  ring_nf at *
  sorry

/-- Algebra from the both-odd package. -/
theorem dividedBothOddPackage_identities_target
    {A N m n a b c d : ℤ}
    (h : DividedBothOddPackage A N m n a b c d) :
    a ^ 2 + c ^ 2 = 3 * b ^ 2 ∧
    a ^ 2 + b ^ 2 = d ^ 2 := by
  -- Use `m = 2*a^2 + c^2`, then the equations for `m+n` and `2*m-n`.
  ring_nf at *
  sorry

/-- The both-odd package is impossible by mod 4. -/
theorem dividedBothOddPackage_false_target
    {A N m n a b c d : ℤ}
    (h : DividedBothOddPackage A N m n a b c d) :
    False := by
  -- From `Odd n` and `n=c^2`, get `Odd c`.
  -- From the identity, get `a^2 + c^2 = 3*b^2`.
  -- Mod 4: any square plus an odd square is 1 or 2, but 3*b^2 is 0 or 3.
  sorry

/-- Unit theorem for the surviving package, assuming no nonconstant four-square AP. -/
theorem dividedMEvenPackage_unit_target
    (hnoAP : NoNonconstantFourSquaresAP)
    {A N S m n a b c d : ℤ}
    (hbad : PositivePrimitiveEisensteinBadUnordered A N S)
    (hbranch : DividedSquareBranch A N S m n)
    (hpack : DividedMEvenPackage A N m n a b c d) :
    A = 1 ∧ N = 1 ∧ S = 1 := by
  -- Use `dividedMEvenPackage_to_fourSquaresAP_target hpack`.
  -- `hnoAP` gives `c=b=d=a` because all are positive.
  -- Then `m=2*a^2` and `n=a^2`.
  -- `IsCoprime m n` forces `a=1`.
  -- The package gives `A=a*b=1`, `N=c*d=1`.
  -- Finally `3*S = m^2-m*n+n^2 = 3`, hence `S=1`.
  sorry

/-- Final route for the requested statement. -/
theorem dividedSquareBranchUnitOrDescends_from_factorization_and_fourAP_target
    (hfac : DividedSquareBranchFactorizationStatement)
    (hnoAP : NoNonconstantFourSquaresAP) :
    DividedSquareBranchUnitOrDescendsStatement := by
  intro A N S m n hbad hbranch
  rcases hfac hbad hbranch with hE | hM | hO
  · rcases hE with ⟨a,b,c,d,hpack⟩
    exact False.elim (dividedNEvenPackage_false_target hpack)
  · rcases hM with ⟨a,b,c,d,hpack⟩
    exact Or.inl (dividedMEvenPackage_unit_target hnoAP hbad hbranch hpack)
  · rcases hO with ⟨a,b,c,d,hpack⟩
    exact False.elim (dividedBothOddPackage_false_target hpack)

end MazurProof.RationalPointsN12
```

## 7. Minimal implementation order

1. Prove the gcd/valuation table, preferably with `IsCoprime` statements after removing known common factors instead of fighting integer gcd normalization.
2. Prove `dividedSquareBranch_to_reduced_target`; it is a useful sanity check that the `3` went to the right factors.
3. Prove `DividedSquareBranchFactorizationStatement` by combining the gcd table, parity split, and squarefree-factor extraction for `1`, `2`, `3`, and `6`.
4. Prove the two mod-4 contradictions.
5. Prove `dividedMEvenPackage_to_fourSquaresAP_target` by `ring_nf`/linear arithmetic.
6. Supply `NoNonconstantFourSquaresAP`, either directly by Fermat descent or by a bridge to the existing checked Euler descent.
7. Prove `DividedSquareBranchUnitOrDescendsStatement` by the final route above.

The only substantial new mathematical residual is `FourSquaresAP`. The other two packages are elementary contradictions.

## 8. False tempting shortcuts

```text
Claim: 3 ∤ (2*m-n).
False: 3 ∣ (2*m-n) is forced.
Counterexample: m=2,n=1.

Claim: 3 ∣ (m-n).
False: 3 ∤ (m-n) is forced.
Counterexample: m=2,n=1.

Claim: v_3(m+n)=v_3(2*m-n)=1.
False from gcd/divisibility alone. The true statement is that the nonsquare factor 3 goes into those factors, and after division by 3 their quotients are coprime.

Claim: the divided branch is raw after rescaling.
False: after `m+n=3*p`, `2*m-n=3*q`, the equations are crossed:
  A^2=p*(2*q-p), N^2=q*(2*p-q).

Claim: the surviving package directly gives the raw EulerSquarePair.
False: it gives `FourSquaresAP c b d a`; a new bridge/residual is needed.
```
