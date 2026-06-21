/-
DISCHARGE A1: rational_torsion_two_invariant_factors → data constructor (assumption 6→5).
Assembly from: C1 invariant-factor algebra (✅ InvariantFactors.lean), C2 finiteness (✅ from
mordell_weil_fg), K2 geomNTorsion rank-2 (in build). Field obligations FIXED by TorsionStructureData
signature (Axioms.lean): m n, m_pos n_pos, dvd_mn, has_structure (∃ inj ZMod m×ZMod n →+ Point),
has_point_order_n (∃P, addOrderOf P = n), card_eq (torsionSet.ncard = m*n).

Construction:
  N := Nat.card (RatTors E)  [RatTors E := AddCommGroup.torsion (E⁄ℚ).Point]
  hfin : Finite (RatTors E)                                   -- C2
  ι₀ : RatTors E →+ geomNTorsion N  (base-change point to ℚbar, killed by N)  -- FRONT (needs K2 area)
  hι₀ : Injective ι₀                                          -- Point.map_injective
  b  : geomNTorsion N ≃ₗ[ZMod N] (Fin 2→ZMod N)               -- K2
  ι  : RatTors E →+ (ZMod N × ZMod N)  := (toProd ∘ b ∘ ι₀)   -- compose, injective
  ⟨m,n,hm,hn,hmn,hcard,⟨e⟩⟩ := C1 hN ι hι                     -- e : RatTors E ≃+ ZMod m × ZMod n
  THEN (this file's job — pure assembly, K2-independent):
    has_structure   := ⟨(e.symm : ZMod m×ZMod n →+ RatTors E).comp (incl RatTors↪Point), inj⟩
    has_point_order := e.symm (0,1) has addOrderOf = n  (AddEquiv.addOrderOf_eq, ZMod.addOrderOf_one,
                       Prod.addOrderOf, incl preserves addOrderOf)
    card_eq         := (torsionSet E).ncard = Nat.card (RatTors E) = m*n  (Set.ncard = Nat.card subtype)
-/
import Mathlib
import FLT.Assumptions.MazurProof.Axioms
import FLT.Assumptions.MazurProof.TorsionFinite
-- import FLT.EllipticCurve.Torsion  -- for geomNTorsion/K2 once wired

open scoped WeierstrassCurve.Affine

namespace MazurProof

-- BACK-HALF (K2-independent assembly): TorsionStructureData from a RatTors equivalence.
-- This is the part to build NOW; the front (ι₀, K2) lands when geomNTorsion rank-2 is ready.
noncomputable def torsionStructureData_of_equiv
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n)
    (hcard : (torsionSet E).ncard = m * n)
    (e : (AddCommGroup.torsion (E⁄ℚ).Point) ≃+ (ZMod m × ZMod n)) :
    TorsionStructureData E := by
  let T : AddSubgroup (E⁄ℚ).Point := AddCommGroup.torsion (E⁄ℚ).Point
  let incl : T →+ (E⁄ℚ).Point := T.subtype
  refine
    { m := m
      n := n
      m_pos := hm
      n_pos := hn
      dvd_mn := hmn
      has_structure := ?_
      has_point_order_n := ?_
      card_eq := hcard }
  · refine ⟨incl.comp e.symm.toAddMonoidHom, ?_⟩
    exact T.subtype_injective.comp e.symm.injective
  · refine ⟨incl (e.symm (0, 1)), ?_⟩
    calc
      addOrderOf (incl (e.symm (0, 1))) = addOrderOf (e.symm (0, 1)) :=
        addOrderOf_injective incl T.subtype_injective (e.symm (0, 1))
      _ = addOrderOf ((0, 1) : ZMod m × ZMod n) :=
        (addOrderOf_injective e.symm.toAddMonoidHom e.symm.injective (0, 1)).trans
          (by simp)
      _ = Nat.lcm (addOrderOf (0 : ZMod m)) (addOrderOf (1 : ZMod n)) := by
        rw [Prod.addOrderOf]
      _ = n := by
        rw [addOrderOf_zero, ZMod.addOrderOf_one, Nat.lcm_comm, Nat.lcm_one_right]

end MazurProof
