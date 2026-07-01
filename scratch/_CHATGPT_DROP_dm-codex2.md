# Q2959 dm-codex2: shrinking Kubert C12 Tate-table residual B

Namespace: `MazurProof.KubertBridgeN12`.

Target file: `FLT/Assumptions/MazurProof/KubertBridgeN12.lean`.

I could not fetch the local WIP file through the GitHub connector. This is written against the declarations in the prompt and the usual Mathlib affine Weierstrass group-law API.

## Executive recommendation

Do **not** try to prove the whole residual

```lean
kubert_C12_table_of_tate_origin_order12
```

directly. Replace it by three small order-to-algebra lemmas:

```lean
theorem tate_c_ne_zero_of_origin_order12 : c ≠ 0
theorem tate_sixP_den_ne_zero_of_origin_order12 : b - c - c ^ 2 ≠ 0
theorem tateC12_K_eq_zero_of_origin_order12 : tateC12_K b c = 0
```

Then the axiom replacement is one line using the checked theorem you already have:

```lean
kubert_C12_table_of_tate_K b c hb hDelta hOrder hc h6 hK
```

The feasible proof route is:

```text
1. Prove the explicit Tate group-law formula 3P = (c, b-c).
2. Use the negation formula to prove:
   c = 0              -> 3P = -P       -> 4P = 0  -> order divides 4, contradiction to 12.
   b-c-c^2 = 0        -> 3P = -3P      -> 6P = 0  -> order divides 6, contradiction to 12.
3. From order 12, Q := 3P satisfies 4Q = 0.
4. Use a division-polynomial/core lemma:
   4Q = 0 and Q=(c,b-c) -> tatePsi4CoreAt3P b c = 0.
5. Use checked `tatePsi4CoreAt3P_eq_c_mul_K` and `c≠0` to get `K=0`.
```

The first theorem to attack is therefore **`tate_three_nsmul_origin_eq`**. It immediately unlocks `c≠0`, `b-c-c²≠0`, and feeds the `ψ₄` vanishing statement.

## 0. API probes

Paste these in `KubertBridgeN12.lean` near the scratch area.

```lean
#check tateW
#check tateOriginAffine
#check tateC12_K
#check tatePsi4CoreAt3P
#check tatePsi4CoreAt3P_eq_c_mul_K
#check kubert_C12_table_of_tate_K
#check kubert_C12_table_of_tate_origin_order12

#check addOrderOf
#check addOrderOf_dvd_iff_nsmul_eq_zero
#check nsmul_eq_zero_iff_dvd_addOrderOf
#check addOrderOf_nsmul_eq_zero

#check WeierstrassCurve.Affine.Point.add
#check WeierstrassCurve.Affine.Point.neg
#check WeierstrassCurve.Affine.Point.some
#check WeierstrassCurve.Affine.Point.ext
```

Search if names differ:

```bash
rg "addOrderOf_dvd|nsmul_eq_zero.*addOrderOf|divisionPolynomial|psi|Division" \
  .lake/packages/mathlib/Mathlib -n
rg "tatePsi4CoreAt3P|tateC12_K|tateOriginAffine|tateW" \
  FLT/Assumptions/MazurProof/KubertBridgeN12.lean scratch -n
```

## 1. Final axiom replacement wrapper

This is the target wrapper after proving the three order-to-algebra lemmas.

```lean
import Mathlib.Tactic
-- existing imports of KubertBridgeN12.lean

namespace MazurProof.KubertBridgeN12

/-- Checked replacement for residual B once the three order-to-algebra lemmas are proved. -/
noncomputable def kubert_C12_table_of_tate_origin_order12_checked
    (b c : ℚ) (hb : b ≠ 0)
    (hDelta : (tateW b c).Δ ≠ 0)
    (hOrder : addOrderOf (tateOriginAffine b c hb) = 12) :
    KubertC12TateTableModel b c hb hDelta hOrder := by
  have hc : c ≠ 0 :=
    tate_c_ne_zero_of_origin_order12 b c hb hDelta hOrder
  have h6 : b - c - c ^ 2 ≠ 0 :=
    tate_sixP_den_ne_zero_of_origin_order12 b c hb hDelta hOrder
  have hK : tateC12_K b c = 0 :=
    tateC12_K_eq_zero_of_origin_order12 b c hb hDelta hOrder
  exact kubert_C12_table_of_tate_K b c hb hDelta hOrder hc h6 hK

end MazurProof.KubertBridgeN12
```

Once this checks, replace call sites of the axiom by `kubert_C12_table_of_tate_origin_order12_checked`, then delete or deprecate the axiom.

## 2. Group-law points to expose

The local formulas you want are:

```text
P  = (0,0)
2P = (b, b*c)
3P = (c, b-c)
-P = (0,b)
-(3P) = (c,c^2)
```

For the Tate normal form

```text
y² + (1-c)xy - b*y = x³ - b*x²
```

negation is

```text
-(x,y) = (x, -y - (1-c)*x + b).
```

So for `Q=(c,b-c)`,

```text
-Q = (c, -(b-c) - (1-c)c + b) = (c,c²).
```

Define point constructors only if they are not already present locally.

```lean
namespace MazurProof.KubertBridgeN12

open scoped WeierstrassCurve.Affine

/-- Point `(b, b*c)` on the Tate model.  Proof should be direct `simp [tateW]; ring`. -/
theorem tate_twoP_nonsingular
    (b c : ℚ) (hb : b ≠ 0) (hDelta : (tateW b c).Δ ≠ 0) :
    WeierstrassCurve.Affine.Nonsingular
      (WeierstrassCurve.toAffine (tateW b c)) b (b * c) := by
  -- Usually either follows from `hDelta` plus curve equation, or direct nonsingularity.
  -- Try:
  --   simp [WeierstrassCurve.Affine.Nonsingular, tateW, hb, hDelta]
  --   constructor goals by ring/field_simp.
  -- If this is painful, avoid exposing this theorem and prove 2P equality by `ext` using
  -- the point returned by the addition formula.
  ...

/-- Point `(c, b-c)` on the Tate model. -/
theorem tate_threeP_nonsingular
    (b c : ℚ) (hb : b ≠ 0) (hDelta : (tateW b c).Δ ≠ 0) :
    WeierstrassCurve.Affine.Nonsingular
      (WeierstrassCurve.toAffine (tateW b c)) c (b - c) := by
  -- Same note as above.
  ...

noncomputable def tateTwoPAffine
    (b c : ℚ) (hb : b ≠ 0) (hDelta : (tateW b c).Δ ≠ 0) :
    WeierstrassCurve.Affine.Point (tateW b c) :=
  WeierstrassCurve.Affine.Point.some b (b * c)
    (tate_twoP_nonsingular b c hb hDelta)

noncomputable def tateThreePAffine
    (b c : ℚ) (hb : b ≠ 0) (hDelta : (tateW b c).Δ ≠ 0) :
    WeierstrassCurve.Affine.Point (tateW b c) :=
  WeierstrassCurve.Affine.Point.some c (b - c)
    (tate_threeP_nonsingular b c hb hDelta)

end MazurProof.KubertBridgeN12
```

If the local point type is `WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine (tateW b c))` instead of `Point (tateW b c)`, use the spelling already accepted by `tateOriginAffine`.

## 3. First theorem to attack: `3P = (c,b-c)`

Do not start from the K polynomial. Prove the affine group-law formula first.

```lean
namespace MazurProof.KubertBridgeN12

/-- Doubling formula for the Tate origin. -/
theorem tate_two_nsmul_origin_eq
    (b c : ℚ) (hb : b ≠ 0) (hDelta : (tateW b c).Δ ≠ 0) :
    (2 : ℕ) • tateOriginAffine b c hb = tateTwoPAffine b c hb hDelta := by
  -- Expected denominator in the tangent formula is `-b`, nonzero by `hb`.
  have hden : (-b : ℚ) ≠ 0 := by simpa using neg_ne_zero.mpr hb
  -- Route:
  --   change tateOriginAffine b c hb + tateOriginAffine b c hb = _
  --   unfold tateOriginAffine tateTwoPAffine
  --   simp [WeierstrassCurve.Affine.Point.add, WeierstrassCurve.Affine.Point.neg,
  --     tateW, hb, hden]
  --   ext <;> field_simp [hb] <;> ring
  -- Depending on local API, the addition formula may have named lemmas for same-x/double case.
  change tateOriginAffine b c hb + tateOriginAffine b c hb = tateTwoPAffine b c hb hDelta
  ext <;> simp [tateOriginAffine, tateTwoPAffine, tateW, hb, hden] <;> field_simp [hb] <;> ring

/-- Addition formula `2P + P = 3P = (c,b-c)`. -/
theorem tate_three_nsmul_origin_eq
    (b c : ℚ) (hb : b ≠ 0) (hDelta : (tateW b c).Δ ≠ 0) :
    (3 : ℕ) • tateOriginAffine b c hb = tateThreePAffine b c hb hDelta := by
  have h2 := tate_two_nsmul_origin_eq b c hb hDelta
  -- Expected denominator in adding `(b,bc)` to `(0,0)` is `b`, nonzero by `hb`.
  -- Route:
  --   change (2 • P) + P = _
  --   rw [h2]
  --   unfold tateOriginAffine tateTwoPAffine tateThreePAffine
  --   simp [Point.add, tateW, hb]
  --   ext <;> field_simp [hb] <;> ring
  change (2 : ℕ) • tateOriginAffine b c hb + tateOriginAffine b c hb =
    tateThreePAffine b c hb hDelta
  rw [h2]
  ext <;> simp [tateOriginAffine, tateTwoPAffine, tateThreePAffine, tateW, hb] <;>
    field_simp [hb] <;> ring

end MazurProof.KubertBridgeN12
```

If `ext` does not work because affine points include an infinity constructor, first force both sides to be `some` via the addition formula branch. The branch conditions should be only `hb`/`-b≠0`.

The failed scratch attempts likely got stuck because the `Point.add` simplifier split into vertical/tangent branches. Add the denominator facts explicitly before `simp`:

```lean
have hb0 : b ≠ 0 := hb
have hnb0 : -b ≠ 0 := by simpa using neg_ne_zero.mpr hb
have hb_ne_0x : b - 0 ≠ 0 := by simpa using hb
simp [hb0, hnb0, hb_ne_0x]
```

## 4. Negation formulas

These are much easier than addition and should be direct.

```lean
namespace MazurProof.KubertBridgeN12

/-- Under `c=0`, `3P=(0,b)=-P`. -/
theorem tate_three_nsmul_origin_eq_neg_origin_of_c_eq_zero
    (b c : ℚ) (hb : b ≠ 0) (hDelta : (tateW b c).Δ ≠ 0)
    (hc0 : c = 0) :
    (3 : ℕ) • tateOriginAffine b c hb = - tateOriginAffine b c hb := by
  rw [tate_three_nsmul_origin_eq b c hb hDelta]
  subst c
  -- both sides are `(0,b)` by the Tate negation formula.
  ext <;> simp [tateOriginAffine, tateThreePAffine, tateW]

/-- If `b-c-c^2=0`, then `3P` is a 2-torsion point: `3P = -3P`. -/
theorem tate_three_nsmul_origin_eq_neg_self_of_six_den_eq_zero
    (b c : ℚ) (hb : b ≠ 0) (hDelta : (tateW b c).Δ ≠ 0)
    (h6zero : b - c - c ^ 2 = 0) :
    (3 : ℕ) • tateOriginAffine b c hb =
      - ((3 : ℕ) • tateOriginAffine b c hb) := by
  rw [tate_three_nsmul_origin_eq b c hb hDelta]
  -- RHS negation of `(c,b-c)` has y-coordinate `c^2`.
  -- `h6zero` rewrites `b-c = c^2`.
  have hy : b - c = c ^ 2 := by linarith
  ext <;> simp [tateThreePAffine, tateW, hy] <;> ring

end MazurProof.KubertBridgeN12
```

## 5. Order-theory utilities

These proofs avoid curve-specific APIs.

```lean
namespace MazurProof.KubertBridgeN12

private theorem nsmul_eq_zero_of_addOrderOf_eq
    {G : Type*} [AddMonoid G] {P : G} {n : ℕ}
    (h : addOrderOf P = n) :
    n • P = 0 := by
  -- `addOrderOf_dvd_iff_nsmul_eq_zero : addOrderOf P ∣ n ↔ n • P = 0`
  exact (addOrderOf_dvd_iff_nsmul_eq_zero.mp (by rw [h]))

private theorem order12_not_dvd_four
    {G : Type*} [AddMonoid G] {P : G}
    (hOrder : addOrderOf P = 12) :
    ¬ (4 : ℕ) • P = 0 := by
  intro h4
  have hdiv : addOrderOf P ∣ 4 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h4
  rw [hOrder] at hdiv
  norm_num at hdiv

private theorem order12_not_dvd_six
    {G : Type*} [AddMonoid G] {P : G}
    (hOrder : addOrderOf P = 12) :
    ¬ (6 : ℕ) • P = 0 := by
  intro h6
  have hdiv : addOrderOf P ∣ 6 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h6
  rw [hOrder] at hdiv
  norm_num at hdiv

end MazurProof.KubertBridgeN12
```

If `addOrderOf_dvd_iff_nsmul_eq_zero` has the opposite `.mp`/`.mpr` orientation in the local Mathlib, the goal messages will make the swap obvious.

## 6. Derive `c ≠ 0`

```lean
namespace MazurProof.KubertBridgeN12

theorem tate_c_ne_zero_of_origin_order12
    (b c : ℚ) (hb : b ≠ 0)
    (hDelta : (tateW b c).Δ ≠ 0)
    (hOrder : addOrderOf (tateOriginAffine b c hb) = 12) :
    c ≠ 0 := by
  intro hc0
  let P := tateOriginAffine b c hb
  have h3neg : (3 : ℕ) • P = -P := by
    simpa [P] using
      tate_three_nsmul_origin_eq_neg_origin_of_c_eq_zero b c hb hDelta hc0
  have h4P : (4 : ℕ) • P = 0 := by
    -- `4P = 3P + P = -P + P = 0`.
    change ((3 : ℕ) + 1) • P = 0
    rw [add_nsmul, h3neg]
    simp
  exact order12_not_dvd_four hOrder h4P

end MazurProof.KubertBridgeN12
```

## 7. Derive `b - c - c² ≠ 0`

```lean
namespace MazurProof.KubertBridgeN12

theorem tate_sixP_den_ne_zero_of_origin_order12
    (b c : ℚ) (hb : b ≠ 0)
    (hDelta : (tateW b c).Δ ≠ 0)
    (hOrder : addOrderOf (tateOriginAffine b c hb) = 12) :
    b - c - c ^ 2 ≠ 0 := by
  intro h6zero
  let P := tateOriginAffine b c hb
  have h3self : (3 : ℕ) • P = - ((3 : ℕ) • P) := by
    simpa [P] using
      tate_three_nsmul_origin_eq_neg_self_of_six_den_eq_zero b c hb hDelta h6zero
  have h6P : (6 : ℕ) • P = 0 := by
    -- `6P = 2*(3P) = 3P + 3P = -3P + 3P = 0`.
    have htwo : (2 : ℕ) • ((3 : ℕ) • P) = 0 := by
      rw [two_nsmul, h3self]
      simp
    simpa [nsmul_nsmul, mul_comm, mul_left_comm, mul_assoc] using htwo
  exact order12_not_dvd_six hOrder h6P

end MazurProof.KubertBridgeN12
```

## 8. Vanishing of the `ψ₄` core at `3P`

This is the second theorem to attack after `3P=(c,b-c)`. It should be smaller than the current residual B.

Preferred statement:

```lean
namespace MazurProof.KubertBridgeN12

/-- Division-polynomial/core interface at `Q=3P`.  This is the key small replacement for residual B. -/
theorem tatePsi4CoreAt3P_eq_zero_of_origin_order12
    (b c : ℚ) (hb : b ≠ 0)
    (hDelta : (tateW b c).Δ ≠ 0)
    (hOrder : addOrderOf (tateOriginAffine b c hb) = 12) :
    tatePsi4CoreAt3P b c = 0 := by
  let P := tateOriginAffine b c hb
  let Q := (3 : ℕ) • P
  have h12P : (12 : ℕ) • P = 0 := by
    exact nsmul_eq_zero_of_addOrderOf_eq hOrder
  have h4Q : (4 : ℕ) • Q = 0 := by
    dsimp [Q, P]
    -- `4 • (3 • P) = 12 • P`.
    simpa [nsmul_nsmul, mul_comm, mul_left_comm, mul_assoc] using h12P

  have hQcoords : Q = tateThreePAffine b c hb hDelta := by
    dsimp [Q, P]
    exact tate_three_nsmul_origin_eq b c hb hDelta

  -- Now use the local division-polynomial theorem.  You may have to create this
  -- as a small lemma if Mathlib only gives a general theorem.
  exact tatePsi4CoreAt3P_eq_zero_of_four_nsmul_threeP_eq_zero
    b c hb hDelta hQcoords h4Q

end MazurProof.KubertBridgeN12
```

The missing helper should have this precise shape:

```lean
namespace MazurProof.KubertBridgeN12

/-- Local bridge from `4Q=0` to vanishing of the specialized 4-division core at `Q=(c,b-c)`. -/
theorem tatePsi4CoreAt3P_eq_zero_of_four_nsmul_threeP_eq_zero
    (b c : ℚ) (hb : b ≠ 0)
    (hDelta : (tateW b c).Δ ≠ 0)
    {Q : WeierstrassCurve.Affine.Point (tateW b c)}
    (hQcoords : Q = tateThreePAffine b c hb hDelta)
    (h4Q : (4 : ℕ) • Q = 0) :
    tatePsi4CoreAt3P b c = 0 := by
  -- Route A: use Mathlib division-polynomial API if available.
  -- Search for a theorem of the form:
  --   `n • Point.some x y h = 0 -> divisionPolynomial n x = 0`
  -- or:
  --   `divisionPolynomial 4` evaluated at `(c,b-c)`.
  --
  -- Route B: if there is no useful API, prove this by direct affine group law:
  --   1. Expand `2Q` for `Q=(c,b-c)`.
  --   2. Show `4Q=0` forces the denominator/numerator core to vanish.
  --   3. The numerator is exactly `tatePsi4CoreAt3P b c` by your existing polynomial definitions.
  --
  -- Keep this theorem as the only remaining local algebra target; do not put it as an axiom.
  ...

end MazurProof.KubertBridgeN12
```

This helper is not a new axiom: it is the targeted theorem to prove with Mathlib APIs or direct affine calculation. It is much smaller than `kubert_C12_table_of_tate_origin_order12` because it only says “order 4 at the already-computed point makes the already-defined core vanish.”

Likely Mathlib probes for Route A:

```lean
#check WeierstrassCurve.divisionPolynomial
#check WeierstrassCurve.Affine.divisionPolynomial
#check WeierstrassCurve.Affine.Point.divisionPolynomial
#check WeierstrassCurve.Affine.Point.nsmul_eq_zero_iff_divisionPolynomial_eq_zero
#check WeierstrassCurve.Affine.Point.divisionPolynomial_eq_zero_of_nsmul_eq_zero
```

If no theorem exists, route B is still feasible because `Q=(c,b-c)` and `4Q=0` is only one specialized calculation.

## 9. Derive `K=0`

This part is already easy because you have `tatePsi4CoreAt3P_eq_c_mul_K`.

```lean
namespace MazurProof.KubertBridgeN12

theorem tateC12_K_eq_zero_of_origin_order12
    (b c : ℚ) (hb : b ≠ 0)
    (hDelta : (tateW b c).Δ ≠ 0)
    (hOrder : addOrderOf (tateOriginAffine b c hb) = 12) :
    tateC12_K b c = 0 := by
  have hc : c ≠ 0 :=
    tate_c_ne_zero_of_origin_order12 b c hb hDelta hOrder
  have hpsi : tatePsi4CoreAt3P b c = 0 :=
    tatePsi4CoreAt3P_eq_zero_of_origin_order12 b c hb hDelta hOrder
  have hprod : c * tateC12_K b c = 0 := by
    -- theorem checked locally: `tatePsi4CoreAt3P b c = c * tateC12_K b c`
    simpa [tatePsi4CoreAt3P_eq_c_mul_K] using hpsi
  exact (mul_eq_zero.mp hprod).resolve_left hc

end MazurProof.KubertBridgeN12
```

If `simpa [tatePsi4CoreAt3P_eq_c_mul_K]` does not rewrite because the theorem is not tagged as a simp theorem or is oriented, use:

```lean
  have hcore : tatePsi4CoreAt3P b c = c * tateC12_K b c :=
    tatePsi4CoreAt3P_eq_c_mul_K b c
  rw [hcore] at hpsi
  exact (mul_eq_zero.mp hpsi).resolve_left hc
```

## 10. Smaller replacement residual, if needed temporarily

If division-polynomial vanishing is not done today, shrink residual B to exactly this statement:

```lean
def TateC12Psi4VanishesFromOriginOrder12Statement : Prop :=
  ∀ (b c : ℚ) (hb : b ≠ 0)
    (hDelta : (tateW b c).Δ ≠ 0)
    (hOrder : addOrderOf (tateOriginAffine b c hb) = 12),
    tatePsi4CoreAt3P b c = 0
```

Then the replacement wrapper consumes this **one small residual**:

```lean
noncomputable def kubert_C12_table_of_tate_origin_order12_from_psi4_residual
    (hPsi : TateC12Psi4VanishesFromOriginOrder12Statement)
    (b c : ℚ) (hb : b ≠ 0)
    (hDelta : (tateW b c).Δ ≠ 0)
    (hOrder : addOrderOf (tateOriginAffine b c hb) = 12) :
    KubertC12TateTableModel b c hb hDelta hOrder := by
  have hc : c ≠ 0 := tate_c_ne_zero_of_origin_order12 b c hb hDelta hOrder
  have h6 : b - c - c ^ 2 ≠ 0 :=
    tate_sixP_den_ne_zero_of_origin_order12 b c hb hDelta hOrder
  have hpsi : tatePsi4CoreAt3P b c = 0 := hPsi b c hb hDelta hOrder
  have hK : tateC12_K b c = 0 := by
    have hcore : tatePsi4CoreAt3P b c = c * tateC12_K b c :=
      tatePsi4CoreAt3P_eq_c_mul_K b c
    rw [hcore] at hpsi
    exact (mul_eq_zero.mp hpsi).resolve_left hc
  exact kubert_C12_table_of_tate_K b c hb hDelta hOrder hc h6 hK
```

This is a strict improvement over the current axiom: it leaves only the order-12-to-ψ₄-vanishing bridge, not the table algebra or the exceptional denominators.

## 11. Practical edit order

1. Prove `tate_two_nsmul_origin_eq`.
2. Prove `tate_three_nsmul_origin_eq`.
3. Prove the two negation consequences:
   * `tate_three_nsmul_origin_eq_neg_origin_of_c_eq_zero`
   * `tate_three_nsmul_origin_eq_neg_self_of_six_den_eq_zero`
4. Add `tate_c_ne_zero_of_origin_order12` and `tate_sixP_den_ne_zero_of_origin_order12`.
5. Prove or temporarily isolate `tatePsi4CoreAt3P_eq_zero_of_origin_order12`.
6. Add `tateC12_K_eq_zero_of_origin_order12`.
7. Replace the residual axiom by `kubert_C12_table_of_tate_origin_order12_checked`.

The only genuinely hard proof is step 5 if Mathlib lacks a convenient division-polynomial theorem. Steps 1-4 are group-law coordinate calculations and order-divisibility arguments; steps 6-7 are already algebraic wrappers around checked code.
