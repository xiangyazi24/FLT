import Mathlib
import FLT.Assumptions.MazurProof.Axioms
import FLT.Assumptions.MazurProof.WeilPairingInterface

/-!
# Weil Pairing: Thin Shim over WeilPairingInterface

## Architecture (Q2055)

This file is a thin shim that exposes the old theorem names while delegating
the mathematical substance to `WeilPairingInterface.lean`.

* `fullRationalTorsion_order_le_two` delegates to `weil_interface_bridge`
  (which carries the sorry for the EC-theoretic inputs) and then applies
  `isPrimitiveRoot_rat_order_le_two` from `RootsOfUnity.lean`.
* `not_hasFullRationalTorsion_of_three_le` and the casework in
  `weil_pairing_gives_primitive_root` are fully proved (no sorry).

**Sorry count in this file: 0.**  The sole remaining sorry lives in
`WeilPairingInterface.weil_interface_bridge`.
-/

open scoped WeierstrassCurve.Affine
open MazurProof.WeilPairingInterface

namespace MazurProof

/-! ## Base cases: m = 1 and m = 2 -/

private lemma primitive_root_one : IsPrimitiveRoot (1 : ℚ) 1 :=
  IsPrimitiveRoot.one

private lemma primitive_root_two : IsPrimitiveRoot (-1 : ℚ) 2 where
  pow_eq_one := by norm_num
  dvd_of_pow_eq_one l hl := by
    rcases Nat.even_or_odd l with ⟨k, hk⟩ | ho
    · exact ⟨k, by omega⟩
    · exfalso; linarith [ho.neg_one_pow (α := ℚ)]

/-! ## Core obstruction: HasFullRationalTorsion E m → m ≤ 2

Delegates to `WeilPairingInterface.weil_interface_bridge` (which encapsulates
the Galois-equivariant Weil pairing construction) and then closes with
`isPrimitiveRoot_rat_order_le_two` (the only primitive roots in ℚ have
order ≤ 2).
-/

theorem fullRationalTorsion_order_le_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    m ≤ 2 := by
  obtain ⟨ζ, hζ⟩ := weil_interface_bridge E hm hfull
  exact isPrimitiveRoot_rat_order_le_two hζ

theorem not_hasFullRationalTorsion_of_three_le
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm3 : 3 ≤ m) :
    ¬ HasFullRationalTorsion E m := by
  intro hfull
  have hm_pos : 0 < m := by omega
  have hm_le_two : m ≤ 2 :=
    fullRationalTorsion_order_le_two (E := E) (m := m) hm_pos hfull
  omega

/-! ## Main theorem: Direct casework on m ≤ 2 -/

theorem weil_pairing_gives_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  by_cases hm1 : m = 1
  · subst hm1
    exact ⟨1, primitive_root_one⟩
  by_cases hm2 : m = 2
  · subst hm2
    exact ⟨-1, primitive_root_two⟩
  have hm3 : 3 ≤ m := by omega
  exact False.elim (not_hasFullRationalTorsion_of_three_le (E := E) hm3 hfull)

end MazurProof
