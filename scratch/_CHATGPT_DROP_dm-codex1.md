# Q2407 (dm-codex1): non-circular Fermat/Euler descent plan for four rational squares in AP

Goal:

```lean
def FourRatSquaresAPConst : Prop :=
  ∀ {w x y z : ℚ},
    x^2 - w^2 = y^2 - x^2 →
    y^2 - x^2 = z^2 - y^2 →
      w^2 = x^2 ∧ x^2 = y^2 ∧ y^2 = z^2
```

This drop gives a Lean-oriented classical descent route.  It does **not** use the E1 rational-point theorem and does **not** route through the N=12 elliptic curve.  The cleanest formalization boundary is not a one-line `not_fermat_42` substitution; it is Euler/van der Poorten's descent on the auxiliary condition

```text
4*A^2 + D^2 and 16*A^2 + D^2 are both squares.
```

Reference for the formulas: Alf van der Poorten, *Fermat's Four Squares Theorem*, arXiv:0712.3850.  The relevant proof starts from four integer squares

```text
x - 6n, x - 2n, x + 2n, x + 6n
```

and descends through the auxiliary pair `(A,D)`.

---

## 1. Integer primitive theorem statement

The most useful Lean residual is not directly the AP theorem; it is an auxiliary no-solution theorem plus an AP-to-aux bridge.

```lean
import Mathlib.Tactic
import Mathlib.Data.Int.Parity
-- likely also useful, depending on current Mathlib names:
-- import Mathlib.NumberTheory.PythagoreanTriples

namespace MazurProof.RationalPointsN12

/-- Four integer squares in AP.  No ordering/sign convention. -/
def IntFourSqAP (a b c d : ℤ) : Prop :=
  b^2 - a^2 = c^2 - b^2 ∧
  c^2 - b^2 = d^2 - c^2

/-- Nonconstant AP, phrased by nonzero common gap. -/
def IntFourSqAPNonconstant (a b c d : ℤ) : Prop :=
  b^2 - a^2 ≠ 0

/-- A primitive 4-tuple of roots.  In code, using `natAbs` usually avoids
sign pain around `Int.gcd`. -/
def IntPrimitive4 (a b c d : ℤ) : Prop :=
  Nat.gcd (Nat.gcd (Nat.gcd a.natAbs b.natAbs) c.natAbs) d.natAbs = 1

/-- Main integer theorem, primitive form. -/
def IntFourSquaresAPPrimitiveConst : Prop :=
  ∀ {a b c d : ℤ},
    IntPrimitive4 a b c d →
    IntFourSqAP a b c d →
    a^2 = b^2 ∧ b^2 = c^2 ∧ c^2 = d^2

/-- Euler/van der Poorten auxiliary condition.
`D` is intended odd and coprime to `A`; the two displayed numbers are squares. -/
def EulerAux (A D : ℤ) : Prop :=
  A ≠ 0 ∧ D ≠ 0 ∧
  Odd D ∧ Nat.Coprime A.natAbs D.natAbs ∧
  ∃ S R : ℤ,
    S^2 = 4*A^2 + D^2 ∧
    R^2 = 16*A^2 + D^2

/-- No nonzero Euler auxiliary pair.  This is the core infinite descent theorem. -/
def EulerAuxNoSolution : Prop :=
  ¬ ∃ A D : ℤ, EulerAux A D

/-- The actual proof package for the integer AP theorem. -/
theorem intFourSquaresAPPrimitiveConst_of_eulerAuxNoSolution
    (hEuler : EulerAuxNoSolution) :
    IntFourSquaresAPPrimitiveConst := by
  -- Prove by contradiction:
  -- 1. normalize a primitive nonconstant AP to odd pairwise-coprime roots;
  -- 2. rewrite the square terms as `x-6n, x-2n, x+2n, x+6n`;
  -- 3. use `primitiveAP_to_EulerAux` below to produce `EulerAux A D`;
  -- 4. contradiction with `hEuler`.
  -- Constant AP is immediate by `nlinarith`.
  intro a b c d hprim hAP
  by_cases hgap : b^2 - a^2 = 0
  · rcases hAP with ⟨h1, h2⟩
    have hb : b^2 = a^2 := by nlinarith
    have hc : c^2 = b^2 := by nlinarith [h1, hgap]
    have hd : d^2 = c^2 := by nlinarith [h2, h1, hgap]
    exact ⟨hb.symm, hc.symm, hd.symm⟩
  · exfalso
    -- call `primitive_nonconstant_AP_to_EulerAux hprim hAP hgap`
    -- exact hEuler ⟨A, D, hAux⟩
    sorry

end MazurProof.RationalPointsN12
```

The theorem above contains one intentional `sorry` in this roadmap: it should be replaced by the normalization and descent bridges below.  Do **not** expose this as a final theorem with `sorry`; expose the lower-level bridge statements and prove them one by one.

---

## 2. Normalization lemmas: signs, parity, gcd, symmetric form

### 2.1 Rational to integer common denominator

For the rational theorem, first clear denominators of the roots, not of the square terms.

```lean
namespace MazurProof.RationalPointsN12

/-- Denominator clearing for rational roots in a four-square AP. -/
theorem rat_four_sq_AP_to_int
    {w x y z : ℚ}
    (h1 : x^2 - w^2 = y^2 - x^2)
    (h2 : y^2 - x^2 = z^2 - y^2)
    (hnon : x^2 - w^2 ≠ 0) :
    ∃ M W X Y Z : ℤ,
      M ≠ 0 ∧
      W = M * w ∧ X = M * x ∧ Y = M * y ∧ Z = M * z ∧
      IntFourSqAP W X Y Z ∧
      IntFourSqAPNonconstant W X Y Z := by
  -- Choose `M` as the product or lcm of the four positive denominators.
  -- Use `Rat.num`, `Rat.den`, or existing denominator clearing lemmas.
  -- After multiplying h1/h2 by `M^2`, all terms are integer squares.
  sorry

/-- Divide an integer AP by the common gcd of the four roots. -/
theorem int_four_sq_AP_primitive_reduction
    {a b c d : ℤ}
    (hAP : IntFourSqAP a b c d)
    (hnon : IntFourSqAPNonconstant a b c d) :
    ∃ a' b' c' d' g : ℤ,
      g ≠ 0 ∧
      a = g*a' ∧ b = g*b' ∧ c = g*c' ∧ d = g*d' ∧
      IntPrimitive4 a' b' c' d' ∧
      IntFourSqAP a' b' c' d' ∧
      IntFourSqAPNonconstant a' b' c' d' := by
  -- Let `g = gcd4(a,b,c,d)` as an integer from Nat gcd of natAbs.
  -- Since equations are homogeneous in the roots squared, divide all roots by g.
  sorry

end MazurProof.RationalPointsN12
```

### 2.2 Primitive nonconstant AP roots are odd and pairwise coprime

For a primitive nonconstant integer AP:

* all four roots are odd;
* the common difference of square terms is divisible by `8`, hence also by `4`;
* the roots are pairwise coprime.

Lean statements:

```lean
namespace MazurProof.RationalPointsN12

theorem primitive_AP_roots_odd
    {a b c d : ℤ}
    (hprim : IntPrimitive4 a b c d)
    (hAP : IntFourSqAP a b c d)
    (hnon : IntFourSqAPNonconstant a b c d) :
    Odd a ∧ Odd b ∧ Odd c ∧ Odd d := by
  -- Mod 4: square residues are 0 or 1.
  -- A four-term AP in `{0,1}` mod 4 is constant mod 4.
  -- If one root is even, all squares are 0 mod 4; then all roots even,
  -- contradicting primitive.  Therefore all roots odd.
  sorry

theorem primitive_AP_pairwise_coprime
    {a b c d : ℤ}
    (hprim : IntPrimitive4 a b c d)
    (hAP : IntFourSqAP a b c d)
    (hnon : IntFourSqAPNonconstant a b c d) :
    Nat.Coprime a.natAbs b.natAbs ∧
    Nat.Coprime a.natAbs c.natAbs ∧
    Nat.Coprime a.natAbs d.natAbs ∧
    Nat.Coprime b.natAbs c.natAbs ∧
    Nat.Coprime b.natAbs d.natAbs ∧
    Nat.Coprime c.natAbs d.natAbs := by
  -- If a prime divides two roots, it divides the corresponding two square terms.
  -- Since all square terms are in one AP, it divides the common gap and then all
  -- four square terms, hence all four roots, contradicting primitive.
  sorry

end MazurProof.RationalPointsN12
```

### 2.3 Symmetric odd form

Given square terms in AP, set the midpoint and quarter-gap by

```text
common gap = 4*n,
terms = x - 6*n, x - 2*n, x + 2*n, x + 6*n.
```

For primitive nonconstant AP, all terms are odd squares, so the common gap is divisible by `8`; the representation above is integral.

```lean
namespace MazurProof.RationalPointsN12

/-- Symmetric form of a primitive nonconstant AP of odd squares. -/
theorem primitive_AP_symmetric_form
    {a b c d : ℤ}
    (hprim : IntPrimitive4 a b c d)
    (hAP : IntFourSqAP a b c d)
    (hnon : IntFourSqAPNonconstant a b c d) :
    ∃ x n : ℤ,
      n ≠ 0 ∧ Odd x ∧
      a^2 = x - 6*n ∧
      b^2 = x - 2*n ∧
      c^2 = x + 2*n ∧
      d^2 = x + 6*n := by
  -- Let `gap = b^2-a^2`.  Since roots are odd, `8 | gap`; in particular `4 | gap`.
  -- Put `n = gap/4` and `x = (b^2+c^2)/2`.
  -- Then the four equations are linear arithmetic.
  sorry

end MazurProof.RationalPointsN12
```

---

## 3. Pythagorean parametrization formulas

Use the primitive triple parameterization in the following variant, which avoids `/2` terms.

For a primitive Pythagorean triple whose even leg is divisible by `4`:

```text
E = 4*u*v,
O = ±(4*u^2 - v^2),
H = 4*u^2 + v^2,
Nat.Coprime (2*u).natAbs v.natAbs,
```

with `v` odd.  This is the same as the usual formula with parameters `(2u,v)`.

Lean-facing statement:

```lean
namespace MazurProof.RationalPointsN12

/-- Primitive Pythagorean parametrization in the `4uv` variant. -/
theorem primitive_pythagorean_even_leg_param4
    {E O H : ℤ}
    (hpy : E^2 + O^2 = H^2)
    (hprim : Nat.gcd (Nat.gcd E.natAbs O.natAbs) H.natAbs = 1)
    (hE4 : ∃ q : ℤ, E = 4*q)
    (hOodd : Odd O) :
    ∃ u v : ℤ,
      Nat.Coprime (2*u).natAbs v.natAbs ∧
      E = 4*u*v ∧
      (O = 4*u^2 - v^2 ∨ O = v^2 - 4*u^2) ∧
      H = 4*u^2 + v^2 := by
  -- Import/search Mathlib's PythagoreanTriples API first.
  -- If the API is awkward, prove this local theorem from the standard primitive
  -- triple theorem with parameters `m=2u`, `n=v`.
  sorry

end MazurProof.RationalPointsN12
```

How to search current Mathlib by type/name:

```lean
-- Try these in a scratch Lean file:
import Mathlib.Tactic
import Mathlib.NumberTheory.PythagoreanTriples

#check PythagoreanTriple
#check IsPythagoreanTriple
#check not_fermat_42
#find _ ^ 2 + _ ^ 2 = _ ^ 2
#find (_ : ℕ) ^ 4 + (_ : ℕ) ^ 4 = (_ : ℕ) ^ 2
```

Shell greps that are usually faster than guessing names:

```bash
grep -R "Pythagorean" .lake/packages/mathlib/Mathlib/NumberTheory .lake/packages/mathlib/Mathlib/Data -n
grep -R "not_fermat_42\|fermat_42\|Fermat4" .lake/packages/mathlib/Mathlib -n
grep -R "\^ 4.*\^ 4.*\^ 2" .lake/packages/mathlib/Mathlib/NumberTheory -n
```

If the imported API is too Nat-oriented, keep the local theorem above over `ℤ` and prove it once by converting to `ℕ` with `natAbs`.

---

## 4. AP-to-EulerAux bridge

Assume primitive nonconstant AP in symmetric form:

```text
a^2 = x - 6n,
b^2 = x - 2n,
c^2 = x + 2n,
d^2 = x + 6n.
```

Because the roots are pairwise coprime, set

```text
y := a*b*c*d.
```

Then

```text
y^2 = (x^2 - 4n^2) * (x^2 - 36n^2)
    = (x^2 - 20n^2)^2 - (16n^2)^2.
```

So

```text
(16*n^2)^2 + y^2 = (x^2 - 20*n^2)^2.
```

This is a primitive Pythagorean triple.  Parameterize it:

```text
16*n^2 = 4*u*v,
y = ±(4*u^2 - v^2),
x^2 - 20*n^2 = 4*u^2 + v^2,
Nat.Coprime (2u) v.
```

Since `u*v = 4*n^2` and `(2u,v)=1`, coprimality forces

```text
u = 4*A^2,
v = D^2,
A*D = ± n,
D odd.
```

Now use

```text
4*u^2 + v^2 = x^2 - 20*n^2
```

and `u*v = 4*n^2` to rewrite it as

```text
4*u^2 + v^2 = x^2 - 5*u*v.
```

Therefore

```text
(4*u + v) * (u + v) = x^2.
```

The two factors are coprime; hence each is a square:

```text
4*u + v = 16*A^2 + D^2 = R^2,
u + v = 4*A^2 + D^2 = S^2.
```

So `(A,D)` satisfies `EulerAux`.

Lean bridge:

```lean
namespace MazurProof.RationalPointsN12

theorem primitive_nonconstant_AP_to_EulerAux
    {a b c d : ℤ}
    (hprim : IntPrimitive4 a b c d)
    (hAP : IntFourSqAP a b c d)
    (hnon : IntFourSqAPNonconstant a b c d) :
    ∃ A D : ℤ, EulerAux A D := by
  -- Steps:
  -- 1. get `x,n` from `primitive_AP_symmetric_form`;
  -- 2. define `y := a*b*c*d`;
  -- 3. prove the Pythagorean identity
  --      (16*n^2)^2 + y^2 = (x^2 - 20*n^2)^2;
  -- 4. prove primitive/coprime hypotheses;
  -- 5. parameterize with `primitive_pythagorean_even_leg_param4`;
  -- 6. from `u*v=4*n^2` and `Nat.Coprime (2u).natAbs v.natAbs`, prove
  --      `u = 4*A^2`, `v = D^2`;
  -- 7. derive `(4*u+v)*(u+v)=x^2` and use coprime-product-square to show
  --      both factors are squares.
  sorry

end MazurProof.RationalPointsN12
```

Reusable coprime-square product lemmas needed here:

```lean
namespace MazurProof.RationalPointsN12

/-- Nonnegative coprime integer factors of a square are squares. -/
theorem Int_coprime_mul_eq_sq_of_nonneg
    {a b z : ℤ}
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hcop : Nat.Coprime a.natAbs b.natAbs)
    (h : a * b = z^2) :
    ∃ r s : ℤ, a = r^2 ∧ b = s^2 := by
  -- This is the reusable helper from Q2292/Q2380 direction.
  -- Prove by prime factorization or existing Mathlib squarefree/associated API.
  sorry

end MazurProof.RationalPointsN12
```

---

## 5. Descent step: smaller EulerAux pair

This is the core non-circular theorem.

### 5.1 Descent theorem statement

Use the positive measure

```text
measure(A,D) = |A*D|.natAbs
```

or simply `Int.natAbs (A*D)`.

```lean
namespace MazurProof.RationalPointsN12

/-- One strict descent step for the Euler auxiliary condition. -/
theorem EulerAux_descent_step
    {A D : ℤ}
    (hAD : EulerAux A D) :
    ∃ a d : ℤ,
      EulerAux a d ∧
      (a*d).natAbs < (A*D).natAbs := by
  sorry

/-- No nonzero Euler auxiliary pair, by well-founded descent on `natAbs (A*D)`. -/
theorem eulerAuxNoSolution : EulerAuxNoSolution := by
  -- Suppose a solution exists. Choose one minimizing `(A*D).natAbs` using
  -- `Nat.find`/well-founded minimal counterexample.  Apply `EulerAux_descent_step`
  -- to get a strictly smaller one, contradiction.
  sorry

end MazurProof.RationalPointsN12
```

### 5.2 Explicit descent formulas

Assume

```text
S^2 = 4*A^2 + D^2,
R^2 = 16*A^2 + D^2,
A ≠ 0, D odd, gcd(A,D)=1.
```

Apply primitive Pythagorean parametrization to the first square:

```text
(2*A)^2 + D^2 = S^2.
```

There exist coprime integers `U,V` such that

```text
U*V = A,
U^2 - V^2 = ε₁ * D,        ε₁ ∈ {+1,-1}.
```

Apply primitive Pythagorean parametrization to the second square:

```text
(4*A)^2 + D^2 = R^2.
```

There exist coprime integers `U',V'` such that

```text
U' * V' = A,
4*U'^2 - V'^2 = ε₂ * D,    ε₂ ∈ {+1,-1}.
```

Adjust signs of `V`/`V'` if needed; the equations use squares, so signs can be normalized to a common `ε`:

```text
ε*D = U^2 - V^2 = 4*U'^2 - V'^2.
```

Now refine the two coprime factorizations of `A`:

```text
U  = 2*a*b,
V  = c*d,
U' = 2*a*c,
V' = b*d,
A  = 2*a*b*c*d,
```

where `2*a`, `b`, `c`, `d` are pairwise coprime.  Substitution gives

```text
ε*D = 4*a^2*b^2 - c^2*d^2
    = 16*a^2*c^2 - b^2*d^2.
```

Equating the two expressions gives the key identity

```text
b^2 * (4*a^2 + d^2) = c^2 * (16*a^2 + d^2).        (★)
```

Because `2*a,b,c,d` are pairwise coprime, one proves

```text
Nat.Coprime b.natAbs c.natAbs,
Nat.Coprime (4*a^2 + d^2).natAbs (16*a^2 + d^2).natAbs.
```

The second gcd proof is elementary:

* any common divisor divides `12*a^2` and `d^2`;
* since `gcd(a,d)=1`, it divides `12`;
* the two numbers are odd, so no factor `2`;
* modulo `3`, if both are divisible by `3`, then `a^2 + d^2 ≡ 0 (mod 3)`, impossible for coprime `a,d` unless both are divisible by `3`.

Therefore from `(★)` both factors are squares:

```text
∃ S' R', S'^2 = 4*a^2 + d^2 ∧ R'^2 = 16*a^2 + d^2.
```

So `(a,d)` satisfies `EulerAux`.

Strict size decrease:

```text
A = 2*a*b*c*d,
so |a*d| ≤ |A|/2 < |A| ≤ |A*D|       since D ≠ 0.
```

This is the descent.

Lean skeleton for the core algebraic refinement:

```lean
namespace MazurProof.RationalPointsN12

/-- Refinement of two coprime factorizations of the same integer. -/
theorem two_coprime_factorizations_refine
    {U V U' V' A : ℤ}
    (hUV : U*V = A)
    (hUV' : U'*V' = A)
    (hcop1 : Nat.Coprime U.natAbs V.natAbs)
    (hcop2 : Nat.Coprime U'.natAbs V'.natAbs)
    -- plus parity facts: `Even U`, `Even U'`, `Odd V`, `Odd V'`
    :
    ∃ a b c d : ℤ,
      U = 2*a*b ∧ V = c*d ∧ U' = 2*a*c ∧ V' = b*d ∧
      A = 2*a*b*c*d ∧
      -- pairwise coprime package for `2*a,b,c,d`
      True := by
  -- Prove by gcd-splitting:
  -- a = common part of U/2 and U'/2;
  -- b = remaining part of U/2 and V';
  -- c = remaining part of U'/2 and V;
  -- d = common part of V and V'.
  sorry

/-- The algebraic heart of the descent after the factorization refinement. -/
theorem EulerAux_descent_algebra
    {a b c d D : ℤ}
    (hD1 : 4*a^2*b^2 - c^2*d^2 = D)
    (hD2 : 16*a^2*c^2 - b^2*d^2 = D)
    -- pairwise coprime hypotheses on `2*a,b,c,d`
    :
    ∃ S R : ℤ,
      S^2 = 4*a^2 + d^2 ∧
      R^2 = 16*a^2 + d^2 := by
  have hkey : b^2 * (4*a^2 + d^2) = c^2 * (16*a^2 + d^2) := by
    nlinarith [hD1, hD2]
  -- Then use coprime cancellation/product-square reasoning as described above.
  sorry

end MazurProof.RationalPointsN12
```

This is the place where Lean work is nontrivial but local.  It is pure gcd/factorization arithmetic; no elliptic curve API appears.

---

## 6. Rational common-denominator wrapper

Once the integer primitive theorem is proved, the rational theorem is straightforward.

```lean
namespace MazurProof.RationalPointsN12

/-- Rational four-squares AP theorem from the primitive integer theorem. -/
theorem fourRatSquaresAPConst_of_int
    (hInt : IntFourSquaresAPPrimitiveConst) :
    FourRatSquaresAPConst := by
  intro w x y z h1 h2
  by_cases hnon : x^2 - w^2 = 0
  · have hxw : x^2 = w^2 := by nlinarith
    have hyx : y^2 = x^2 := by nlinarith [h1, hnon]
    have hzy : z^2 = y^2 := by nlinarith [h1, h2, hnon]
    exact ⟨hxw.symm, hyx.symm, hzy.symm⟩
  · -- clear denominators to integer roots
    rcases rat_four_sq_AP_to_int h1 h2 hnon with
      ⟨M, W, X, Y, Z, hM, hW, hX, hY, hZ, hAPi, hnon_i⟩
    rcases int_four_sq_AP_primitive_reduction hAPi hnon_i with
      ⟨W', X', Y', Z', g, hg, rflW, rflX, rflY, rflZ, hprim, hAPp, hnonp⟩
    have hc := hInt hprim hAPp
    -- Lift equality of primitive integer squares back through multiplication by `g^2`
    -- and then divide by `M^2` using `M ≠ 0`.
    -- This is all `nlinarith` + `field_simp [hM]`.
    sorry

/-- Final non-circular proof package. -/
theorem fourRatSquaresAPConst_from_euler_descent :
    FourRatSquaresAPConst := by
  exact fourRatSquaresAPConst_of_int
    (intFourSquaresAPPrimitiveConst_of_eulerAuxNoSolution eulerAuxNoSolution)

end MazurProof.RationalPointsN12
```

For integration, keep the wrapper theorem separate from the descent theorem.  The cover residuals from Q2403 should consume only:

```lean
hAP : FourRatSquaresAPConst
```

Then `fourRatSquaresAPConst_from_euler_descent` is the independent producer of `hAP`.

---

## 7. Minimal theorem DAG to implement

Recommended file-level DAG:

```text
Primitive Pythagorean parametrization over Int
  + coprime product square lemmas
  + primitive AP normalization
        |
        v
primitive_nonconstant_AP_to_EulerAux
        |
        v
EulerAux_descent_step
        |
        v
eulerAuxNoSolution
        |
        v
IntFourSquaresAPPrimitiveConst
        |
        v
FourRatSquaresAPConst
        |
        v
Q2403 cover residuals:
  coverQ_3_2_6_AP_const
  coverQ_neg1_neg2_2_AP_const
  coverQ_3_2_6_forces_X_eq_three
  coverQ_neg1_neg2_2_forces_X_eq_neg_one
```

Do **not** use `E1` rational-point classification to prove `FourRatSquaresAPConst`.  That would be circular for the full-cover route.  Also do not expect `not_fermat_42` alone to close this: it may help prove the Fermat right-triangle theorem, but the four-AP theorem here needs the Euler auxiliary descent or an equivalent independent theorem.

---

## 8. Practical Mathlib search checklist

I did not verify exact current Mathlib names in this connector-only drop.  Search by type and equation shape:

```bash
grep -R "Pythagorean" .lake/packages/mathlib/Mathlib -n
grep -R "IsPythagorean\|PythagoreanTriple" .lake/packages/mathlib/Mathlib -n
grep -R "not_fermat_42\|Fermat4\|fermat_42" .lake/packages/mathlib/Mathlib -n
grep -R "Coprime.*mul.*sq\|sq.*mul.*Coprime" .lake/packages/mathlib/Mathlib -n
grep -R "natAbs" .lake/packages/mathlib/Mathlib/NumberTheory -n | head -50
```

And inside Lean:

```lean
#import Mathlib.Tactic
#import Mathlib.NumberTheory.PythagoreanTriples

#check not_fermat_42
#find _ ^ 2 + _ ^ 2 = _ ^ 2
#find Nat.Coprime _ _ → _ * _ = _ ^ 2 → _
#find (_ : ℤ) ^ 2 = _ ^ 2
```

If `#find` is unavailable in your environment, use grep plus `#check` on candidate names.

---

## 9. Why this route is non-circular

The descent proves `FourRatSquaresAPConst` from:

* primitive Pythagorean triple parametrization;
* gcd/coprime-square factorization facts;
* well-founded descent on a natural number measure.

It does not invoke:

* E1 rational points;
* the N=12 quartic classification;
* elliptic-curve group law;
* the full-cover residual wrappers.

Therefore it is safe as an independent producer for the AP residuals in the E1 full-cover proof.
