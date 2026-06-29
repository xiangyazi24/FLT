# Q2186 Lean/Math audit: honest boundary for the N=12 denominator residual

This answers the route question for the curve

```text
E : w^2 = u^3 - u^2 - 4*u + 4 = (u + 2) * (u - 1) * (u - 2).
```

The short version is: the odd-prime sign-splitting lemmas are useful local infrastructure, but they are not a realistic standalone route to the full N=12 obstruction.  The honest arithmetic boundary should be either a rational-points classification for this affine curve, or a two-piece boundary consisting of denominator integrality plus integral-point degeneracy.  The eventual certificate should be a 2-descent/Selmer computation plus torsion/integral-point enumeration, not a false global sign argument.

## 1. Is the denominator residual essentially equivalent to `E(ℚ)` finite/rank zero?

Not literally equivalent, but it sits at almost the same arithmetic depth.

The residual

```lean
def N12NoNontrivialSquareDenominatorResidual : Prop :=
  ∀ A B C : ℤ,
    1 < B →
    Int.gcd A B = 1 →
    C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2) →
    False
```

says: if an affine rational point has primitive square-denominator form

```text
u = A / B^2,
w = C / B^3,
```

then `B = 1`.  For an integral monic Weierstrass model, rational `u`-coordinates naturally have square denominator, so this is exactly an `x`-integrality theorem for rational points on this curve.

However, `B = 1` alone does **not** classify the integral points.  It only says every rational point has integral `u`.  To get the obstruction theorem, one still needs to prove that the integral points have

```text
u ∈ {-2, 0, 1, 2, 4}
```

with the corresponding `w` values

```text
(-2, 0), (0, ±2), (1, 0), (2, 0), (4, ±6).
```

So the logical relationship is:

```text
full rational-point classification
  ⇒ denominator residual + integral-point degeneracy
  ⇒ obstruction-curve degeneracy.
```

The reverse implication is false as stated: denominator residual alone does not imply rank zero or the exact finite torsion list; it only excludes nonintegral `u`-coordinates.

In practice, proving the denominator residual without proving something very close to rank zero / rational-point classification is unlikely.  The local prime-power sign splitting is a fragment of a descent, not a complete descent.

## 2. Is there a realistic elementary continuation from the prime-power sign splitting?

There is no short purely local continuation from

```text
B^2 ∣ (C - z^3) * (C + z^3)
```

to the full residual.  The odd-prime splitting proves that for each odd prime-power contribution to `B^2`, that contribution lands in exactly one of the two factors.  But the chosen sign can vary with the prime.  After CRT, one obtains a square root of `1` modulo the odd part of `B^2`, not a global sign `±1`.

A possible continuation is a genuine descent.  For this curve the natural descent is the full rational 2-torsion descent, because

```text
u^3 - u^2 - 4u + 4 = (u + 2)(u - 1)(u - 2).
```

For a rational point not among the 2-torsion points, define the squareclass data

```text
δ(P) = (u + 2, u - 1, u - 2) ∈ (ℚ*/ℚ*²)^3,
```

with product a square because

```text
(u + 2)(u - 1)(u - 2) = w^2.
```

Outside the bad set

```text
S = {∞, 2, 3},
```

all valuations in the three squareclasses are even.  The prime `3` enters because the differences of the three roots include `3`, and the prime `2` enters because the model and the root differences include powers of `2`.  Thus each squareclass representative can be taken from the finite set

```text
{±1, ±2, ±3, ±6}
```

up to the product-one condition.  The corresponding covering equations are of the shape

```text
u + 2 = d₁ r₁^2,
u - 1 = d₂ r₂^2,
u - 2 = d₃ r₃^2,
d₁ d₂ d₃ ∈ ℚ*²,
```

or equivalently the difference equations

```text
d₁ r₁^2 - d₂ r₂^2 = 3,
d₁ r₁^2 - d₃ r₃^2 = 4,
d₂ r₂^2 - d₃ r₃^2 = 1.
```

A certified finite computation would check local solubility of these covers at `∞`, `2`, and `3`, keep only the surviving Selmer classes, and show that the Selmer group has the same `𝔽₂`-dimension as the visible torsion quotient.  This proves rank zero.  Then Lutz--Nagell / torsion enumeration gives the finite point list.

That route is “elementary” only in the sense that it reduces to finitely many congruence checks and explicit genus-one covers.  Mathematically and formally, it is still elliptic-curve descent.  It is not just a continuation of the denominator congruence.

### Where `p = 2` enters

The odd-prime lemma must not include `p = 2`.  If `2 ∣ B`, then `gcd(C,B)=1` and `gcd(z,B)=1` imply `C` and `z` are odd, hence both

```text
C - z^3,
C + z^3
```

are even.  Thus the statement “exactly one sign receives the prime contribution” is false at `2`.  The 2-adic contribution is governed by congruences modulo `8`, `16`, etc., or by the 2-adic local condition in the 2-descent/Selmer computation.

## 3. Clean Lean boundary theorem statements

There are two good boundary styles.

### Boundary A: one affine rational-points theorem

This is the cleanest long-term theorem.  It packages the actual arithmetic fact and keeps the N=12 file independent of elliptic-curve infrastructure.

```lean
import Mathlib

namespace FLT
namespace MazurProof

/-- The affine N=12 obstruction curve. -/
def N12AffineCurve (u w : ℚ) : Prop :=
  w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4

/-- The `u`-coordinates that are degenerate for the N=12 obstruction. -/
def N12DegenerateX (u : ℚ) : Prop :=
  u = (-2 : ℚ) ∨ u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 4

/--
Honest arithmetic boundary: all affine rational points on the N=12 curve are
among the degenerate `u`-coordinates.

This is weaker than listing `w`, but it is enough for the obstruction layer.
-/
axiom n12_affine_rational_points_degenerate_x
    (u w : ℚ)
    (hcurve : N12AffineCurve u w) :
    N12DegenerateX u

/--
Stronger replaceable boundary: exact affine rational point classification.
Use this if later files need the `w`-coordinate too.
-/
axiom n12_affine_rational_points_classified
    (u w : ℚ)
    (hcurve : N12AffineCurve u w) :
    (u = (-2 : ℚ) ∧ w = 0) ∨
    (u = 0 ∧ w = 2) ∨
    (u = 0 ∧ w = -2) ∨
    (u = 1 ∧ w = 0) ∨
    (u = 2 ∧ w = 0) ∨
    (u = 4 ∧ w = 6) ∨
    (u = 4 ∧ w = -6)

/--
Primitive square denominators cannot represent an integer `u` when `1 < B`.
This is the elementary wrapper lemma needed to use the rational-point boundary.
-/
theorem primitive_square_denominator_not_degenerate_x
    (A B : ℤ)
    (hBgt : 1 < B)
    (hcop : Int.gcd A B = 1) :
    ¬ N12DegenerateX ((A : ℚ) / (B : ℚ) ^ 2) := by
  -- Proof route:
  --   * split the five cases `u = -2,0,1,2,4`;
  --   * clear denominators using `field_simp` and `B ≠ 0`;
  --   * obtain `B^2 ∣ A` up to the relevant integer value;
  --   * in all cases get a common divisor of `A` and `B`, or directly
  --     `B ∣ 1`, contradicting `1 < B`.
  -- Useful APIs/tactics:
  --   `field_simp`, `norm_num`, `Int.dvd_coe_gcd`, `exact_mod_cast`, `omega`.
  sorry

/--
Wrapper from the affine rational-point boundary to the existing denominator
residual target.
-/
theorem N12NoNontrivialSquareDenominatorResidual_of_affine_boundary :
    N12NoNontrivialSquareDenominatorResidual := by
  intro A B C hBgt hcop hC
  let u : ℚ := (A : ℚ) / (B : ℚ) ^ 2
  let w : ℚ := (C : ℚ) / (B : ℚ) ^ 3
  have hBne_int : B ≠ 0 := by omega
  have hBne_rat : (B : ℚ) ≠ 0 := by exact_mod_cast hBne_int
  have hcurve : N12AffineCurve u w := by
    -- Clear denominators and use `hC`.
    -- Typical shape:
    --   dsimp [N12AffineCurve, u, w]
    --   field_simp [hBne_rat]
    --   norm_num
    --   nlinarith [hC]
    -- or after `field_simp`, use `ring_nf` plus `hC`.
    sorry
  have hdeg : N12DegenerateX u :=
    n12_affine_rational_points_degenerate_x u w hcurve
  exact primitive_square_denominator_not_degenerate_x A B hBgt hcop hdeg

end MazurProof
end FLT
```

For the existing `obstruction_curve_N12_points_degenerate`, the wrapper should be even simpler: convert the repo’s point representation to `(u,w) : ℚ × ℚ`, apply `n12_affine_rational_points_degenerate_x`, then discharge the five degenerate cases with the already-existing degeneracy predicate.  I would not make the denominator residual itself the top-level arithmetic axiom if the obstruction theorem ultimately needs point degeneracy anyway.

### Boundary B: denominator integrality plus integral-point degeneracy

This is the smallest local boundary if the current file is specifically blocked on `N12NoNontrivialSquareDenominatorResidual`.

```lean
import Mathlib

namespace FLT
namespace MazurProof

/--
Narrow boundary: primitive square-denominator points on the N=12 curve have
trivial denominator.

This is exactly the hard residual as an arithmetic theorem, stated in a form
that the current local target can consume.
-/
axiom n12_square_denominator_trivial
    (A B C : ℤ)
    (hBpos : 0 < B)
    (hcop : Int.gcd A B = 1)
    (hC : C ^ 2 =
      (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2)) :
    B = 1

theorem N12NoNontrivialSquareDenominatorResidual_of_square_denominator_boundary :
    N12NoNontrivialSquareDenominatorResidual := by
  intro A B C hBgt hcop hC
  have hBpos : 0 < B := by omega
  have hB1 : B = 1 :=
    n12_square_denominator_trivial A B C hBpos hcop hC
  omega

/--
Second boundary needed after `B = 1`: all integral points are degenerate.
Replace `N12IntegralPointDegenerate` by the actual predicate already used in
the FLT development.
-/
def N12IntegralPointDegenerate (A C : ℤ) : Prop :=
  A = -2 ∧ C = 0 ∨
  A = 0 ∧ (C = 2 ∨ C = -2) ∨
  A = 1 ∧ C = 0 ∨
  A = 2 ∧ C = 0 ∨
  A = 4 ∧ (C = 6 ∨ C = -6)

axiom n12_integral_points_degenerate
    (A C : ℤ)
    (hC : C ^ 2 = (A - 1) * (A - 2) * (A + 2)) :
    N12IntegralPointDegenerate A C

end MazurProof
end FLT
```

Boundary A is better architecturally.  Boundary B is more convenient if you want to keep moving in the existing square-denominator file.

## 4. How to make the boundary certifiable later

The clean certificate plan is:

1. **Define the curve once.**
   Use a lightweight affine predicate first.  Later, if Mathlib’s elliptic-curve API is mature enough for your needs, connect it to a `WeierstrassCurve`/`EllipticCurve` object.

2. **Prove nonsingularity and record bad primes.**
   The cubic has roots `-2, 1, 2`.  Root differences are `3`, `4`, and `1`, so the bad primes are `2` and `3`.  This matches the finite squareclass set used in a 2-descent.

3. **Torsion enumeration.**
   Use Lutz--Nagell or a direct torsion argument.  The visible torsion points are

   ```text
   O,
   (-2,0), (1,0), (2,0),
   (0,2), (0,-2),
   (4,6), (4,-6).
   ```

   A Lean certificate should not merely quote PARI.  It should include either:
   - a Lutz--Nagell finite candidate list plus evaluation of the curve equation and group-order checks, or
   - reduction-mod-primes torsion bounds plus explicit points and group-law calculations.

4. **Rank zero by 2-descent.**
   Since the curve has full rational 2-torsion, use the descent map

   ```text
   P ↦ (u + 2, u - 1, u - 2) mod squares.
   ```

   A certifiable Selmer computation should include:
   - the finite squareclass universe `{±1, ±2, ±3, ±6}`;
   - the product-one condition;
   - local solubility checks for the associated covers at `∞`, `2`, and `3`;
   - explicit rational points on the surviving covers corresponding to visible torsion;
   - local obstruction certificates for all nonsurviving covers, preferably as finite `ZMod (p^n)` contradictions that `native_decide`, `omega`, `norm_num`, or small custom finite-search lemmas can verify.

   The target theorem should be something like:

   ```lean
   theorem n12_two_selmer_bound_rank_zero :
       -- schematic: the 2-Selmer image has dimension equal to the visible
       -- torsion quotient, hence rank is zero.
       True := by
     -- finite certificate proof
     trivial
   ```

   I would not expose this theorem to the N=12 obstruction file yet.  Keep the obstruction file depending only on `n12_affine_rational_points_degenerate_x` or `n12_affine_rational_points_classified`.

5. **Optional integral-point certificate.**
   If you use Boundary B, prove `n12_integral_points_degenerate` separately.  For integers,

   ```text
   C^2 = (A + 2)(A - 1)(A - 2),
   ```

   and the pairwise gcds of the three factors divide `3`, `4`, and `1`.  This reduces to finitely many squareclass cases supported at `2` and `3`.  It is much easier than the full rational-point theorem, but it only applies after the denominator theorem has already been proved.

6. **PARI/Magma as evidence, not as a Lean proof.**
   The PARI/GP data

   ```text
   conductor 24,
   torsion [8,[4,2]],
   rank 0,
   affine x ∈ {-2,0,1,2,4}
   ```

   is excellent for guiding the certificate.  In Lean, either leave it behind a named axiom/theorem boundary or translate the computation into explicit finite certificates.  Do not make the proof depend on an unchecked transcript.

## 5. Hidden false statements to avoid

### False global sign

Avoid:

```lean
B ^ 2 ∣ C - z ^ 3 ∨ B ^ 2 ∣ C + z ^ 3
```

for composite `B`.  Different odd primes can choose different signs.  The correct statement is per prime power, or equivalently a CRT sign vector / square root of `1` modulo the odd part of `B^2`.

### False inclusion of `p = 2` in the odd split

Avoid any theorem saying the `2`-power contribution lands in exactly one of `C - z^3` and `C + z^3`.  When `C` and `z` are odd, both factors are even.

### False equivalence with rank zero alone

Rank zero alone is not a point classification unless torsion is also enumerated.  The obstruction file wants a finite list of degenerate affine points, not merely `rank = 0`.

### False reliance on denominator residual alone

`N12NoNontrivialSquareDenominatorResidual` only gives `B = 1`.  It does not by itself prove the integral points are exactly the degenerate points.

### False “maximal contribution” language

A theorem with hypothesis

```lean
(p : ℤ) ^ e ∣ B ^ 2
```

only says that this particular `p^e` divisor of `B^2` lands in one factor.  It does not say `e` is the exact valuation.  If exactness is needed later, introduce a valuation/factorization layer explicitly.

## Recommendation

For the current FLT formalization, introduce Boundary A if the next theorem is `obstruction_curve_N12_points_degenerate`; introduce Boundary B only if the immediate blocker is exactly `N12NoNontrivialSquareDenominatorResidual`.

The prime-power sign-splitting lemmas should still be kept.  They are good local descent infrastructure and useful audit evidence.  But the honest mathematical boundary is the rational-point classification of

```text
y^2 = x^3 - x^2 - 4x + 4,
```

or a certified 2-descent plus torsion enumeration proving that classification.