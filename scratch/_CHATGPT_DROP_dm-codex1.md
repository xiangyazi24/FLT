# Q2418-RETRY EulerAux descent step

This drop is only about Euler's descent for the auxiliary condition

```lean
def EulerAux (A D : ℤ) : Prop :=
  A ≠ 0 ∧ D ≠ 0 ∧ Odd D ∧ Nat.Coprime A.natAbs D.natAbs ∧
  ∃ S R : ℤ, S^2 = 4*A^2 + D^2 ∧ R^2 = 16*A^2 + D^2
```

Goal:

```lean
theorem EulerAux_descent_step {A D : ℤ} (hAD : EulerAux A D) :
  ∃ a d : ℤ, EulerAux a d ∧ (a*d).natAbs < (A*D).natAbs
```

The classical descent is the simultaneous Pythagorean-parameter descent for two primitive right triangles with the same odd leg `D` and even legs `2A` and `4A`.

---

## 1. Pythagorean parametrizations and sign/parity normalization

From `EulerAux A D` choose `S R` with

```text
S^2 = (2A)^2 + D^2,
R^2 = (4A)^2 + D^2.
```

Because `Odd D` and `Nat.Coprime A.natAbs D.natAbs`, both triples are primitive:

```text
gcd(2A,D)=1,
gcd(4A,D)=1.
```

Let `E` be the unique choice among `{D,-D}` satisfying

```text
E ≡ -1 (mod 4).        -- equivalently E % 4 = 3 in Lean's Int.mod convention
```

This uniqueness uses `Odd D`: exactly one of `D` and `-D` is `3 mod 4`.

Normalize the first primitive triple by taking the even parameter first:

```text
A = P*Q,
E = P^2 - Q^2,
S^2 = (P^2 + Q^2)^2,
Even P,
Odd Q,
gcd(P,Q)=1.
```

Here `P` is even and `Q` is odd, so `P^2 - Q^2 ≡ -1 (mod 4)`, matching `E`.

Normalize the second primitive triple as the `4uv` variant:

```text
A = U*V,
E = 4*U^2 - V^2,
R^2 = (4*U^2 + V^2)^2,
Odd V,
gcd(2U,V)=1.
```

Since the first parametrization already implies `A=P*Q` with `P` even and `Q` odd, `A` is even.  In the second parametrization `V` is odd and `A=U*V`, hence `U` is even.

Lean-facing combined parametrization theorem:

```lean
import Mathlib.Tactic
import Mathlib.Data.Int.Parity

namespace MazurProof.RationalPointsN12

/-- Euler auxiliary condition. -/
def EulerAux (A D : ℤ) : Prop :=
  A ≠ 0 ∧ D ≠ 0 ∧ Odd D ∧ Nat.Coprime A.natAbs D.natAbs ∧
  ∃ S R : ℤ, S^2 = 4*A^2 + D^2 ∧ R^2 = 16*A^2 + D^2

/-- Sign-normalized simultaneous parametrization of the two primitive triples
`S^2=(2A)^2+D^2` and `R^2=(4A)^2+D^2`.

This packages the ordinary primitive Pythagorean parametrization twice and aligns
both odd legs to the unique `E ∈ {D,-D}` with `E ≡ -1 mod 4`. -/
theorem EulerAux_param
    {A D : ℤ}
    (hAD : EulerAux A D) :
    ∃ E P Q U V : ℤ,
      (E = D ∨ E = -D) ∧
      Even P ∧ Odd Q ∧ Even U ∧ Odd V ∧
      Nat.Coprime P.natAbs Q.natAbs ∧
      Nat.Coprime (2*U).natAbs V.natAbs ∧
      A = P*Q ∧
      A = U*V ∧
      E = P^2 - Q^2 ∧
      E = 4*U^2 - V^2 := by
  -- HARD-ish but standard: call primitive Pythagorean parametrization twice.
  -- First triple: even leg `2A`, odd leg `D`, parameters `P,Q` with P even.
  -- Second triple: even leg `4A`, odd leg `D`, parameters `2U,V` with V odd.
  -- Align signs by the mod-4 normalization of `E`.
  sorry

end MazurProof.RationalPointsN12
```

Implementation detail: if Mathlib's Pythagorean API is Nat-oriented, prove a local Int wrapper once by applying it to `natAbs (2*A)`, `D.natAbs`, `S.natAbs`, then reintroduce signs by changing signs of `P`/`U`.

---

## 2. Precise construction of the smaller `(a,d)`

We now have two coprime factorizations of the same integer:

```text
A = P*Q = U*V,
Even P, Even U,
Odd Q, Odd V,
gcd(P,Q)=1,
gcd(U,V)=1.
```

Refine the two factorizations into a `2×2` grid.  There exist integers `a b c d` such that

```text
P = 2*a*b,
Q = c*d,
U = 2*a*c,
V = b*d,
A = 2*a*b*c*d,
```

and `2a`, `b`, `c`, `d` are pairwise coprime.  In particular:

```text
a ≠ 0,
b ≠ 0,
c ≠ 0,
d ≠ 0,
Odd d,
gcd(a,d)=1.
```

This `a,d` is the smaller Euler auxiliary pair.

Why the grid refinement is true:

```text
g := gcd(P,U)              -- even
P = g*b, U = g*c, gcd(b,c)=1
P*Q = U*V  =>  b*Q = c*V
so c | Q and b | V
Q = c*d, V = b*d
g is even, write g = 2*a.
```

All coprimality facts come from `gcd(P,Q)=1` and `gcd(U,V)=1`.

Lean statements:

```lean
namespace MazurProof.RationalPointsN12

/-- Pairwise coprime package for the four factors `2a,b,c,d`.
You can replace this by a structure if preferred. -/
def PairwiseCoprime2abcd (a b c d : ℤ) : Prop :=
  Nat.Coprime (2*a).natAbs b.natAbs ∧
  Nat.Coprime (2*a).natAbs c.natAbs ∧
  Nat.Coprime (2*a).natAbs d.natAbs ∧
  Nat.Coprime b.natAbs c.natAbs ∧
  Nat.Coprime b.natAbs d.natAbs ∧
  Nat.Coprime c.natAbs d.natAbs

/-- HARD LEMMA 1: refine two coprime factorizations of `A` into a square grid.
This is the main gcd bookkeeping lemma. -/
theorem two_coprime_factorizations_refine_even
    {A P Q U V : ℤ}
    (hPQ : A = P*Q)
    (hUV : A = U*V)
    (hP_even : Even P)
    (hU_even : Even U)
    (hQ_odd : Odd Q)
    (hV_odd : Odd V)
    (hcopPQ : Nat.Coprime P.natAbs Q.natAbs)
    (hcopUV : Nat.Coprime U.natAbs V.natAbs)
    (hA : A ≠ 0) :
    ∃ a b c d : ℤ,
      P = 2*a*b ∧
      Q = c*d ∧
      U = 2*a*c ∧
      V = b*d ∧
      A = 2*a*b*c*d ∧
      a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0 ∧
      Odd d ∧
      PairwiseCoprime2abcd a b c d := by
  -- Gcd-splitting proof.
  -- Let g = gcd(P,U) with sign chosen so P=g*b and U=g*c.
  -- Since P,U are even and Q,V odd, g is even; write g=2a.
  -- From b*Q=c*V and gcd(b,c)=1, write Q=c*d and V=b*d.
  sorry

end MazurProof.RationalPointsN12
```

This factor-refinement lemma is one of the two hardest Lean lemmas in the descent.

---

## 3. Key algebra identity: the new two squares

Substitute the grid refinement into the aligned odd-leg equations:

```text
E = P^2 - Q^2 = (2ab)^2 - (cd)^2
  = 4*a^2*b^2 - c^2*d^2,

E = 4*U^2 - V^2 = 4*(2ac)^2 - (bd)^2
  = 16*a^2*c^2 - b^2*d^2.
```

Equating these gives

```text
4*a^2*b^2 - c^2*d^2 = 16*a^2*c^2 - b^2*d^2.
```

Rearrange:

```text
b^2 * (4*a^2 + d^2) = c^2 * (16*a^2 + d^2).       (★)
```

Set

```text
M := 4*a^2 + d^2,
N := 16*a^2 + d^2.
```

From pairwise coprimality of `2a,b,c,d`:

```text
gcd(b,c)=1,
gcd(M,N)=1.
```

The gcd proof for `M,N` is small but important:

```text
common divisor of M,N divides N-M = 12*a^2,
and also divides 4*M - N = 3*d^2.
Since gcd(a,d)=1, it divides 12 and 3 only.
Both M,N are odd because d is odd, so no factor 2.
Modulo 3, if 3 divides both then a^2+d^2 ≡ 0 mod 3,
which forces 3|a and 3|d, impossible from gcd(a,d)=1.
Therefore gcd(M,N)=1.
```

From `(★)`, `gcd(b,c)=1`, and `gcd(M,N)=1`, the only possibility is

```text
M = c^2,
N = b^2.
```

Thus

```text
c^2 = 4*a^2 + d^2,
b^2 = 16*a^2 + d^2.
```

So `(a,d)` satisfies `EulerAux`, with witnesses

```text
S' = c,
R' = b.
```

Lean statements:

```lean
namespace MazurProof.RationalPointsN12

/-- The rearrangement after substituting the factor grid. -/
theorem EulerAux_key_identity
    {a b c d E : ℤ}
    (hE1 : E = 4*a^2*b^2 - c^2*d^2)
    (hE2 : E = 16*a^2*c^2 - b^2*d^2) :
    b^2 * (4*a^2 + d^2) = c^2 * (16*a^2 + d^2) := by
  nlinarith [hE1, hE2]

/-- HARD LEMMA 2a: the two new factors are coprime. -/
theorem coprime_new_factors
    {a d : ℤ}
    (had : Nat.Coprime a.natAbs d.natAbs)
    (hd_odd : Odd d) :
    Nat.Coprime (4*a^2 + d^2).natAbs (16*a^2 + d^2).natAbs := by
  -- Show a common prime divisor divides 12*a^2 and 3*d^2.
  -- Exclude 2 by oddness of both factors.
  -- Exclude 3 using square residues mod 3 and gcd(a,d)=1.
  sorry

/-- HARD LEMMA 2b: if `b²*M = c²*N`, with the cross-coprimality conditions,
then `M=c²` and `N=b²`.  This is best proved over Nat after positivity. -/
theorem square_factor_balance
    {b c M N : ℤ}
    (hb : b ≠ 0) (hc : c ≠ 0)
    (hMpos : 0 < M) (hNpos : 0 < N)
    (hbc : Nat.Coprime b.natAbs c.natAbs)
    (hMN : Nat.Coprime M.natAbs N.natAbs)
    (h : b^2 * M = c^2 * N) :
    M = c^2 ∧ N = b^2 := by
  -- Convert to Nat using positivity.
  -- From h and gcd(b,c)=1, get c^2 | M and b^2 | N.
  -- Write M=c^2*q and N=b^2*q.
  -- Then q divides gcd(M,N), hence q=1.
  sorry

/-- Algebraic core: after the grid refinement, `(a,d)` has the required two
square witnesses. -/
theorem EulerAux_new_squares_from_grid
    {a b c d E : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hd_odd : Odd d)
    (hpair : PairwiseCoprime2abcd a b c d)
    (hE1 : E = 4*a^2*b^2 - c^2*d^2)
    (hE2 : E = 16*a^2*c^2 - b^2*d^2) :
    c^2 = 4*a^2 + d^2 ∧ b^2 = 16*a^2 + d^2 := by
  have hkey : b^2 * (4*a^2 + d^2) = c^2 * (16*a^2 + d^2) :=
    EulerAux_key_identity hE1 hE2
  have had : Nat.Coprime a.natAbs d.natAbs := by
    -- from `Nat.Coprime (2*a).natAbs d.natAbs`
    rcases hpair with ⟨h2ab, h2ac, h2ad, hbc, hbd, hcd⟩
    -- use coprime of a with d as a factor of 2*a
    sorry
  have hbc : Nat.Coprime b.natAbs c.natAbs := by
    exact hpair.2.2.2.1
  have hMN : Nat.Coprime (4*a^2 + d^2).natAbs (16*a^2 + d^2).natAbs :=
    coprime_new_factors had hd_odd
  have hMpos : 0 < 4*a^2 + d^2 := by nlinarith [sq_nonneg a, sq_nonneg d, hd]
  have hNpos : 0 < 16*a^2 + d^2 := by nlinarith [sq_nonneg a, sq_nonneg d, hd]
  have hbal := square_factor_balance hb hc hMpos hNpos hbc hMN hkey
  exact ⟨hbal.1.symm, hbal.2.symm⟩

end MazurProof.RationalPointsN12
```

The two hardest local arithmetic lemmas are:

```text
two_coprime_factorizations_refine_even
square_factor_balance
```

`coprime_new_factors` is also nontrivial but short: it is a prime-divisibility / mod-3 lemma.

---

## 4. Strict measure decrease

From the grid refinement:

```text
A = 2*a*b*c*d.
```

Then

```text
A*D = (a*d) * (2*b*c*D).
```

Since `b,c,D` are nonzero,

```text
|(2*b*c*D)| ≥ 2.
```

Since `a,d` are nonzero,

```text
|a*d| > 0.
```

Therefore

```text
|a*d| < |a*d| * |2*b*c*D| = |A*D|.
```

Lean statement:

```lean
namespace MazurProof.RationalPointsN12

/-- Strict descent of the measure `natAbs (A*D)` from `A=2abcd`. -/
theorem EulerAux_measure_decrease_from_grid
    {A D a b c d : ℤ}
    (hAgrid : A = 2*a*b*c*d)
    (hD : D ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    (a*d).natAbs < (A*D).natAbs := by
  -- Rewrite `A*D = (a*d) * (2*b*c*D)` and use natAbs_mul.
  -- Let n=(a*d).natAbs > 0 and m=(2*b*c*D).natAbs ≥ 2.
  -- Then n < n*m.
  sorry

end MazurProof.RationalPointsN12
```

---

## 5. Final descent-step assembly

The proof is now mechanical:

1. Use `EulerAux_param` to get `E,P,Q,U,V`.
2. Use `two_coprime_factorizations_refine_even` to get `a,b,c,d`.
3. Substitute into the two odd-leg equations to get the two expressions for `E`.
4. Use `EulerAux_new_squares_from_grid` to get the new square witnesses `c,b`.
5. Package `EulerAux a d`.
6. Use `EulerAux_measure_decrease_from_grid`.

Lean assembly skeleton:

```lean
namespace MazurProof.RationalPointsN12

/-- Final Euler auxiliary descent step. -/
theorem EulerAux_descent_step {A D : ℤ} (hAD : EulerAux A D) :
    ∃ a d : ℤ, EulerAux a d ∧ (a*d).natAbs < (A*D).natAbs := by
  rcases hAD with ⟨hA0, hD0, hDodd, hADcop, S, R, hS, hR⟩
  rcases EulerAux_param (A := A) (D := D)
      ⟨hA0, hD0, hDodd, hADcop, S, R, hS, hR⟩ with
    ⟨E, P, Q, U, V,
      hEpm, hPeven, hQodd, hUeven, hVodd,
      hcopPQ, hcop2UV, hAPQ, hAUV, hEPQ, hEUV⟩

  have hcopUV : Nat.Coprime U.natAbs V.natAbs := by
    -- follows from `Nat.Coprime (2*U).natAbs V.natAbs`
    sorry

  rcases two_coprime_factorizations_refine_even
      hAPQ hAUV hPeven hUeven hQodd hVodd hcopPQ hcopUV hA0 with
    ⟨a, b, c, d,
      hP, hQ, hU, hV, hAgrid,
      ha0, hb0, hc0, hd0, hdodd, hpair⟩

  have hE1 : E = 4*a^2*b^2 - c^2*d^2 := by
    -- substitute P=2ab and Q=cd into E=P²-Q²
    rw [hEPQ, hP, hQ]
    ring
  have hE2 : E = 16*a^2*c^2 - b^2*d^2 := by
    -- substitute U=2ac and V=bd into E=4U²-V²
    rw [hEUV, hU, hV]
    ring

  have hsquares : c^2 = 4*a^2 + d^2 ∧ b^2 = 16*a^2 + d^2 :=
    EulerAux_new_squares_from_grid ha0 hb0 hc0 hd0 hdodd hpair hE1 hE2

  have hacop : Nat.Coprime a.natAbs d.natAbs := by
    -- from `PairwiseCoprime2abcd`: gcd(2a,d)=1 implies gcd(a,d)=1
    sorry

  have hnew : EulerAux a d := by
    refine ⟨ha0, hd0, hdodd, hacop, ?_⟩
    refine ⟨c, b, ?_, ?_⟩
    · exact hsquares.1.symm
    · exact hsquares.2.symm

  have hdrop : (a*d).natAbs < (A*D).natAbs :=
    EulerAux_measure_decrease_from_grid hAgrid hD0 ha0 hb0 hc0 hd0

  exact ⟨a, d, hnew, hdrop⟩

end MazurProof.RationalPointsN12
```

The remaining `sorry`s in this skeleton correspond exactly to small reusable gcd projections or the hard lemmas already isolated above:

```text
EulerAux_param                              -- standard Pythagorean parametrization twice
hcopUV from hcop2UV                         -- easy gcd projection
two_coprime_factorizations_refine_even      -- hard gcd-splitting lemma
EulerAux_new_squares_from_grid              -- hard balance/gcd lemma, with sublemmas
hacop from PairwiseCoprime2abcd             -- easy gcd projection
EulerAux_measure_decrease_from_grid          -- easy Nat inequality
```

---

## 6. Minimal theorem DAG

```text
Primitive Pythagorean parametrization over ℤ
  |
  v
EulerAux_param
  |
  v
two_coprime_factorizations_refine_even       [HARD]
  |
  v
EulerAux_key_identity                         [ring/nlinarith]
  |
  +--> coprime_new_factors                    [mod 4 / mod 3 gcd]
  +--> square_factor_balance                  [HARD divisibility balance]
  |
  v
EulerAux_new_squares_from_grid
  |
  +--> EulerAux_measure_decrease_from_grid    [easy Nat inequality]
  |
  v
EulerAux_descent_step
```

This is the classical descent step in a Lean-friendly form.  The actual smaller pair is precisely the `(a,d)` appearing in the grid refinement

```text
P=2ab, Q=cd, U=2ac, V=bd.
```

The new square witnesses are precisely

```text
S' = c,
R' = b,
```

because the key identity plus coprimality force

```text
c^2 = 4*a^2 + d^2,
b^2 = 16*a^2 + d^2.
```
