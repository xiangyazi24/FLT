import FLT.EllipticCurve.Torsion
import FLT.Assumptions.MazurProof.NoncyclicN10
import FLT.Assumptions.MazurProof.DescentBridgeN14
import FLT.Assumptions.MazurProof.DescentBridgeN16
import FLT.Assumptions.MazurProof.GroupTheory
import FLT.Assumptions.MazurProof.InvariantFactors
import FLT.Assumptions.MazurProof.TorsionFinite
import scratch.DischargeA2

/-!
# Axioms for the Mazur torsion-bound proof scaffold

This file collects the hard mathematical inputs needed to prove the numerical
bound `|E(ℚ)_tors| ≤ 16`.  The axioms are grouped by expected discharge
priority.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

local notation "ℚbar" => AlgebraicClosure ℚ

/-- The torsion subgroup of `E(ℚ)`, as a set, matching `FLT/Assumptions/Mazur.lean`. -/
abbrev torsionSet (E : WeierstrassCurve ℚ) : Set (E⁄ℚ).Point :=
  AddCommGroup.torsion (E⁄ℚ).Point

/-- Placeholder for "all `m`-torsion points of `E` are rational". -/
def HasFullRationalTorsion (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) : Prop :=
  ∃ f : ZMod m × ZMod m →+ (E⁄ℚ).Point, Function.Injective f

/-- Placeholder for "there is a rational point of exact order `n` on `E`". -/
def HasRationalPointOfOrder (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop :=
  ∃ P : (E⁄ℚ).Point, addOrderOf P = n

/--
Placeholder for the structure-theorem assertion
`E(ℚ)_tors ≃ ℤ/mℤ × ℤ/nℤ`, with `m ∣ n`.
-/
def HasTorsionStructure (E : WeierstrassCurve ℚ) [E.IsElliptic] (m n : ℕ) : Prop :=
  ∃ f : ZMod m × ZMod n →+ (E⁄ℚ).Point, Function.Injective f

/-- Placeholder for `E(ℚ)_tors` containing a subgroup `ℤ/2ℤ × ℤ/nℤ`. -/
abbrev ContainsZ2xZn (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop :=
  HasTorsionStructure E 2 n

/--
Finite two-invariant-factor data for the rational torsion subgroup.

The `has_point_order_n` field records the evident element of order `n` in
`ℤ/mℤ × ℤ/nℤ`; it is kept as part of the axiom so the later arithmetic input
can be used without developing finite abelian group theory here.
-/
structure TorsionStructureData (E : WeierstrassCurve ℚ) [E.IsElliptic] where
  m : ℕ
  n : ℕ
  m_pos : 0 < m
  n_pos : 0 < n
  dvd_mn : m ∣ n
  has_structure : HasTorsionStructure E m n
  has_point_order_n : HasRationalPointOfOrder E n
  card_eq : (torsionSet E).ncard = m * n

abbrev RatPts (E : WeierstrassCurve ℚ) [E.IsElliptic] : Type :=
  (E⁄ℚ).Point

abbrev RatTors (E : WeierstrassCurve ℚ) [E.IsElliptic] : Type :=
  AddCommGroup.torsion (RatPts E)

abbrev GeomPts (E : WeierstrassCurve ℚ) [E.IsElliptic] : Type :=
  (E⁄ℚbar).Point

abbrev GeomNTorsion (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℚbar]
    (N : ℕ) : Type :=
  (E.map (algebraMap ℚ ℚbar)).nTorsion N

noncomputable abbrev ratToQbarAlgHom : ℚ →ₐ[ℚ] ℚbar :=
  Algebra.ofId ℚ ℚbar

noncomputable def ratPointBaseChange
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℚbar] :
    RatPts E →+ GeomPts E := by
  exact WeierstrassCurve.Points.map E ratToQbarAlgHom

lemma ratPointBaseChange_injective
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℚbar] :
    Function.Injective (ratPointBaseChange E) := by
  classical
  simpa [ratPointBaseChange, WeierstrassCurve.Points.map, ratToQbarAlgHom] using
    (WeierstrassCurve.Affine.Point.map_injective
      (W' := E) (f := ratToQbarAlgHom))

noncomputable def ratTorsToGeomNTorsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℚbar]
    (N : ℕ)
    (hkill : ∀ T : RatTors E, N • T = 0) :
    RatTors E →+ GeomNTorsion E N where
  toFun T :=
    ⟨ratPointBaseChange E (T : RatPts E), by
      rw [Submodule.mem_torsionBy_iff]
      have hT : N • (T : RatPts E) = 0 := by
        simpa using congrArg Subtype.val (hkill T)
      have hmap : N • ratPointBaseChange E (T : RatPts E) = 0 := by
        simpa using congrArg (ratPointBaseChange E) hT
      change (N : ℤ) • (ratPointBaseChange E (T : RatPts E) : GeomPts E) = 0
      simpa only [natCast_zsmul] using hmap⟩
  map_zero' := by
    apply Subtype.ext
    change ratPointBaseChange E (0 : RatPts E) = (0 : GeomPts E)
    exact map_zero (ratPointBaseChange E)
  map_add' := by
    intro P Q
    apply Subtype.ext
    change
      ratPointBaseChange E ((P + Q : RatTors E) : RatPts E) =
        ratPointBaseChange E (P : RatPts E) + ratPointBaseChange E (Q : RatPts E)
    exact map_add (ratPointBaseChange E) (P : RatPts E) (Q : RatPts E)

lemma ratTorsToGeomNTorsion_injective
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℚbar]
    (N : ℕ)
    (hkill : ∀ T : RatTors E, N • T = 0) :
    Function.Injective (ratTorsToGeomNTorsion E N hkill) := by
  classical
  intro P Q hPQ
  apply Subtype.ext
  apply ratPointBaseChange_injective E
  exact congrArg Subtype.val hPQ

noncomputable def torsionStructureData_of_equiv
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n)
    (hcard : (torsionSet E).ncard = m * n)
    (e : RatTors E ≃+ (ZMod m × ZMod n)) :
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

/-! ## Group A: torsion structure, expected easiest to discharge -/


/--
The rational torsion subgroup has two invariant factors:
`E(ℚ)_tors ≃ ℤ/mℤ × ℤ/nℤ`, with `m ∣ n`, and cardinality `m * n`.
-/
noncomputable def rational_torsion_two_invariant_factors
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    TorsionStructureData E := by
  classical
  let G : Type := RatTors E
  have hfinSet :
      (AddCommGroup.torsion (RatPts E) : Set (RatPts E)).Finite := by
    simpa [RatTors, RatPts] using
      (rational_torsion_finite_alias E)
  letI : Fintype G := by
    dsimp [G, RatTors, RatPts]
    exact hfinSet.fintype
  haveI : Finite G := inferInstance
  let N : ℕ := Nat.card G
  have hN : 0 < N := by
    dsimp [N, G]
    exact Nat.card_pos
  have hkill : ∀ T : G, N • T = 0 := by
    intro T
    have h : Nat.card G • T = 0 :=
      (card_nsmul_eq_zero' (G := G) : Nat.card G • T = 0)
    change Nat.card G • T = 0
    exact h
  let jN : G →+ GeomNTorsion E N :=
    ratTorsToGeomNTorsion E N hkill
  have hjN : Function.Injective jN :=
    ratTorsToGeomNTorsion_injective E N hkill
  have hNbar : (N : ℚbar) ≠ 0 := by
    exact_mod_cast hN.ne'
  let basis : GeomNTorsion E N ≃ₗ[ZMod N] (Fin 2 → ZMod N) :=
    Classical.choice
      (WeierstrassCurve.geomNTorsion_rank_two_linear_algClosure
        (K := ℚ) E (n := N) hNbar)
  let toSq : GeomNTorsion E N ≃+ ZMod N × ZMod N :=
    basis.toAddEquiv.trans (RingEquiv.piFinTwo (fun _ : Fin 2 => ZMod N)).toAddEquiv
  let ι : G →+ ZMod N × ZMod N :=
    toSq.toAddMonoidHom.comp jN
  have hι : Function.Injective ι :=
    toSq.injective.comp hjN
  have hC1 :
      Nonempty
        {mn : ℕ × ℕ //
          0 < mn.1 ∧ 0 < mn.2 ∧ mn.1 ∣ mn.2 ∧
            Nat.card G = mn.1 * mn.2 ∧
            Nonempty (G ≃+ ZMod mn.1 × ZMod mn.2)} := by
    rcases
    finite_add_comm_group_embed_zmod_sq_invariantFactors_card
      (G := G) (N := N) hN ι hι with
      ⟨m, n, hm_pos, hn_pos, hdvd, hcardG, he⟩
    exact ⟨⟨(m, n), hm_pos, hn_pos, hdvd, hcardG, he⟩⟩
  let data :=
    Classical.choice hC1
  let m : ℕ := data.1.1
  let n : ℕ := data.1.2
  have hm_pos : 0 < m := data.2.1
  have hn_pos : 0 < n := data.2.2.1
  have hdvd : m ∣ n := data.2.2.2.1
  have hcardG : Nat.card G = m * n := data.2.2.2.2.1
  let e : G ≃+ ZMod m × ZMod n :=
    Classical.choice data.2.2.2.2.2
  have hcard : (torsionSet E).ncard = m * n := by
    calc
      (torsionSet E).ncard = Nat.card (RatTors E) := by
        simpa [torsionSet, RatTors, RatPts] using
          (Nat.card_coe_set_eq (torsionSet E)).symm
      _ = Nat.card G := by rfl
      _ = m * n := hcardG
  exact torsionStructureData_of_equiv E hm_pos hn_pos hdvd hcard e

/--
If the first invariant factor of the rational torsion subgroup is `m`, then
the full `m`-torsion is rational.
-/
theorem first_invariant_factor_full_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n)
    (hstruct : HasTorsionStructure E m n) :
    HasFullRationalTorsion E m := by
  obtain ⟨embed, hembed⟩ := zmod_prod_contains_square m n hm hn hmn
  obtain ⟨f, hf⟩ := hstruct
  exact ⟨f.comp embed, hf.comp hembed⟩

/-! ## Group B: Weil pairing -/

/--
Weil pairing consequence: if all `m`-torsion points are rational, then `ℚ`
contains a primitive `m`-th root of unity.
-/
theorem weil_pairing_primitive_root (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  exact
    WeierstrassCurve.full_rational_torsion_has_primitive_root
      (E := E) (m := m)
      (WeierstrassCurve.rationalWeilPairingPackage E m)
      hm hfull

/-! ## Group C: noncyclic exclusions -/

/-- No elliptic curve over `ℚ` has rational torsion containing `ℤ/2ℤ × ℤ/nℤ`
for `n ∈ {10, 12, 14, 16}`. -/
theorem no_Z2_cross_Z14
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ContainsZ2xZn E 14 :=
  no_Z2_cross_Z14_from_descent E

theorem no_Z2_cross_Z16
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ContainsZ2xZn E 16 :=
  no_Z2_cross_Z16_from_descent E

theorem no_Z2_cross_Zn_forbidden
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (hn : n = 10 ∨ n = 12 ∨ n = 14 ∨ n = 16) :
    ¬ ContainsZ2xZn E n := by
  rcases hn with rfl | rfl | rfl | rfl
  · exact no_Z2_cross_Z10 E
  · exact no_Z2_cross_Z12 E
  · exact no_Z2_cross_Z14 E
  · exact no_Z2_cross_Z16 E

/-! ## Group D: cyclic order bound, the hard Mazur core -/

/-- No elliptic curve over `ℚ` has a rational point of order at least `17`. -/
axiom no_rational_point_of_order_ge_17
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (hn : 17 ≤ n) :
    ¬ HasRationalPointOfOrder E n

end MazurProof
