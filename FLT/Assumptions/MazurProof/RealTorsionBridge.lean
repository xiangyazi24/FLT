import Mathlib
import FLT.EllipticCurve.Torsion
import FLT.Assumptions.MazurProof.RootsOfUnity

/-!
# Real torsion bridge: replacing Weil pairing with E(ℝ) cardinality bound

This file provides an alternative route to `no_odd_prime_square_in_torsion`
(used in `Axioms.lean` to prove the two-invariant-factor decomposition)
WITHOUT the Weil pairing.

## Strategy

Instead of: Weil pairing → primitive root in ℚ → contradiction,
we use: E(ℚ) ↪ E(ℝ) → |E(ℝ)[p]| ≤ 2p → |(ℤ/pℤ)²| = p² > 2p → contradiction.

## Single axiom

The only hard input is `real_odd_torsion_le`: for an elliptic curve E/ℚ and
odd prime p > 2, the real p-torsion has at most 2p elements.

This follows from E(ℝ) ≅ ℝ/ℤ or ℝ/ℤ × ℤ/2ℤ:
- Identity component E⁰(ℝ) ≅ ℝ/ℤ has p-torsion of size p
- Component group has order 1 or 2
- Odd p-torsion lives entirely in E⁰(ℝ), so |E(ℝ)[p]| = p ≤ 2p

The bound 2p is strictly WEAKER than the true bound p, but suffices for our
application since p² > 2p for p ≥ 3.

## Relation to AddCircle

Mathlib has `AddCircle.card_torsion_le_of_isSMulRegular`, which gives
`|{x : ℝ/ℤ | n•x = 0}| ≤ n`. Once E(ℝ) ≅ ℝ/ℤ × (ℤ/kℤ) is established,
the bound follows immediately.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.RealTorsionBridge

noncomputable section

/-! ## E(ℚ) ↪ E(ℝ): base change along ℚ → ℝ -/

def EQ_to_ER (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (E⁄ℚ).Point →+ (E⁄ℝ).Point :=
  WeierstrassCurve.Points.map E (Algebra.ofId ℚ ℝ)

theorem EQ_to_ER_injective (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Function.Injective (EQ_to_ER E) := by
  unfold EQ_to_ER WeierstrassCurve.Points.map
  exact WeierstrassCurve.Affine.Point.map_injective (W' := E) (f := Algebra.ofId ℚ ℝ)

/-! ## The single real-topology axiom -/

/-- For odd prime `p > 2`, the real `p`-torsion of an elliptic curve has at most `2p` elements.

This is weaker than the true bound `p` (which needs E(ℝ) ≅ ℝ/ℤ × ℤ/kℤ with k | 2).
The `2p` bound suffices because `p² > 2p` for `p ≥ 3`.

Proof path: establish E(ℝ) ≅ AddCircle 1 × (ℤ/kℤ), k ∈ {1,2}, then use
`AddCircle.card_torsion_le_of_isSMulRegular` from Mathlib. -/
axiom real_odd_torsion_le
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) (hp : Nat.Prime p) (hpgt : 2 < p) :
    Finite {P : (E⁄ℝ).Point | (p : ℕ) • P = 0} ∧
    Nat.card {P : (E⁄ℝ).Point | (p : ℕ) • P = 0} ≤ 2 * p

/-! ## Main theorem: no (ℤ/pℤ)² in E(ℚ) for odd prime p -/

/-- For odd prime `p ≥ 3`, `(ℤ/pℤ)²` cannot inject into `E(ℚ)`.

This replaces the Weil pairing route used in `Axioms.lean`. -/
theorem no_zmod_p_square_in_rational_points
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) (hp : Nat.Prime p) (hpgt : 2 < p) :
    ¬ ∃ f : ZMod p × ZMod p →+ (E⁄ℚ).Point, Function.Injective f := by
  rintro ⟨f, hf⟩
  let g := (EQ_to_ER E).comp f
  have hg : Function.Injective g := (EQ_to_ER_injective E).comp hf
  obtain ⟨hfin, hcard⟩ := real_odd_torsion_le E p hp hpgt
  have htors : ∀ x : ZMod p × ZMod p, p • g x = 0 := by
    intro x
    show p • ((EQ_to_ER E) (f x)) = 0
    rw [← (EQ_to_ER E).map_nsmul, ← f.map_nsmul, ZModModule.char_nsmul_eq_zero,
        map_zero, map_zero]
  let toTors : ZMod p × ZMod p → {P : (E⁄ℝ).Point | (p : ℕ) • P = 0} :=
    fun x => ⟨g x, htors x⟩
  have htoTors_inj : Function.Injective toTors := by
    intro a b hab; exact hg (congrArg Subtype.val hab)
  haveI : Finite {P : (E⁄ℝ).Point | (p : ℕ) • P = 0} := hfin
  have hle : Nat.card (ZMod p × ZMod p) ≤
      Nat.card {P : (E⁄ℝ).Point | (p : ℕ) • P = 0} :=
    Nat.card_le_card_of_injective toTors htoTors_inj
  simp [Nat.card_prod] at hle
  have : p * p ≤ 2 * p := le_trans hle hcard
  have : 0 < p := hp.pos
  nlinarith

/-- Version for the torsion subgroup, matching the signature used in `Axioms.lean`. -/
theorem no_odd_prime_square_in_torsion_real
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) (hp : Nat.Prime p) (hpgt : 2 < p) :
    ¬ ∃ f : ZMod p × ZMod p →+ (AddCommGroup.torsion (E⁄ℚ).Point),
        Function.Injective f := by
  rintro ⟨f, hf⟩
  let incl : (AddCommGroup.torsion (E⁄ℚ).Point) →+ (E⁄ℚ).Point :=
    (AddCommGroup.torsion (E⁄ℚ).Point).subtype
  have hincl : Function.Injective incl := Subtype.val_injective
  exact no_zmod_p_square_in_rational_points E p hp hpgt
    ⟨incl.comp f, hincl.comp hf⟩

end

end MazurProof.RealTorsionBridge
