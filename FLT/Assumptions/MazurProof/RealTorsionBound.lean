import Mathlib
import FLT.Assumptions.MazurProof.RealTopologyS3
import FLT.Assumptions.MazurProof.TorsionDefs

/-!
# Route 4B: fullRationalTorsion_order_le_two via real torsion bound

E(ℚ)[m] ↪ E(ℝ)[m] via base change (Mathlib's Point.baseChange).
E(ℝ) is a compact 1-dim real Lie group with ≤ 2 components → #E(ℝ)[m] ≤ 2m.
(ℤ/m)² ↪ E(ℚ) gives m² ≤ 2m → m ≤ 2.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

def nTorsionSet (G : Type*) [AddCommGroup G] (n : ℕ) : Set G :=
  {x | (n : ℕ) • x = 0}

def nTorsionSubgroup (G : Type*) [AddCommGroup G] (n : ℕ) : AddSubgroup G where
  carrier := nTorsionSet G n
  zero_mem' := by simp [nTorsionSet]
  add_mem' := by
    intro a b ha hb
    simp only [nTorsionSet, Set.mem_setOf_eq] at ha hb ⊢
    rw [nsmul_add, ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    simp only [nTorsionSet, Set.mem_setOf_eq] at ha ⊢
    simp [ha]

theorem ncard_le_of_encard_le
    {α : Type*} {s : Set α} (_hs : s.Finite) {m : ℕ}
    (h : s.encard ≤ m) :
    s.ncard ≤ m :=
  (Set.encard_le_coe_iff_finite_ncard_le.mp h).2

theorem addCircle_nTorsionSet_finite_ncard_le
    {T : ℝ} (n : ℕ) (hn : 0 < n) :
    Set.Finite {x : AddCircle T | (n : ℕ) • x = 0} ∧
      Set.ncard {x : AddCircle T | (n : ℕ) • x = 0} ≤ n := by
  classical
  let s : Set (AddCircle T) := {x | (n : ℕ) • x = 0}
  have hs : s.Finite := AddCircle.finite_torsion (p := T) hn
  refine ⟨hs, ncard_le_of_encard_le hs ?_⟩
  exact AddCircle.card_torsion_le_of_isSMulRegular (p := T) n hn.ne' <|
    .of_right_eq_zero_of_smul fun _ ↦ by simp [hn.ne']

theorem nTorsionSet_ncard_le_of_injective_addMonoidHom
    {G H : Type*} [AddCommMonoid G] [AddCommMonoid H]
    (f : G →+ H) (hf : Function.Injective f) (n B : ℕ)
    (hH_finite : Set.Finite {y : H | (n : ℕ) • y = 0})
    (hH_card : Set.ncard {y : H | (n : ℕ) • y = 0} ≤ B) :
    Set.Finite {x : G | (n : ℕ) • x = 0} ∧
      Set.ncard {x : G | (n : ℕ) • x = 0} ≤ B := by
  classical
  let sG : Set G := {x | (n : ℕ) • x = 0}
  let sH : Set H := {y | (n : ℕ) • y = 0}
  have hpre : sG = f ⁻¹' sH := by
    ext x
    constructor
    · intro hx
      change (n : ℕ) • f x = 0
      rw [← f.map_nsmul, hx, f.map_zero]
    · intro hx
      apply hf
      rw [f.map_nsmul, f.map_zero]
      exact hx
  have hG_finite : sG.Finite := by
    rw [hpre]
    exact Set.Finite.preimage (f := f) hf.injOn hH_finite
  refine ⟨hG_finite, ?_⟩
  have hmaps : ∀ x ∈ sG, f x ∈ sH := by
    intro x hx
    change (n : ℕ) • f x = 0
    rw [← f.map_nsmul, hx, f.map_zero]
  have hle : Set.ncard sG ≤ Set.ncard sH :=
    Set.ncard_le_ncard_of_injOn (s := sG) (t := sH) f hmaps hf.injOn hH_finite
  exact hle.trans hH_card

theorem nTorsionSet_ncard_le_of_injective_addCircle
    {G : Type*} [AddCommMonoid G] {T : ℝ}
    (theta : G →+ AddCircle T) (htheta : Function.Injective theta)
    (n : ℕ) (hn : 0 < n) :
    Set.Finite {x : G | (n : ℕ) • x = 0} ∧
      Set.ncard {x : G | (n : ℕ) • x = 0} ≤ n := by
  exact nTorsionSet_ncard_le_of_injective_addMonoidHom theta htheta n n
    (addCircle_nTorsionSet_finite_ncard_le (T := T) n hn).1
    (addCircle_nTorsionSet_finite_ncard_le (T := T) n hn).2

theorem component_ker_nTorsionSet_to_ambient
    {G C : Type*} [AddCommGroup G] [AddCommGroup C]
    (component : G →+ C) (n B : ℕ)
    (hker_finite : Set.Finite {x : component.ker | (n : ℕ) • x = 0})
    (hker_card : Set.ncard {x : component.ker | (n : ℕ) • x = 0} ≤ B) :
    Set.Finite {x : G | (n : ℕ) • x = 0 ∧ component x = 0} ∧
      Set.ncard {x : G | (n : ℕ) • x = 0 ∧ component x = 0} ≤ B := by
  classical
  let sK : Set component.ker := {x | (n : ℕ) • x = 0}
  let sG : Set G := {x | (n : ℕ) • x = 0 ∧ component x = 0}
  have hEquiv : sK ≃ sG :=
    { toFun := fun x => ⟨x.1.1, by
        constructor
        · exact congrArg Subtype.val x.2
        · exact x.1.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.2⟩, by
        ext
        exact x.2.1⟩
      left_inv := by
        intro x
        rcases x with ⟨⟨x, hxcomp⟩, hxT⟩
        rfl
      right_inv := by
        intro x
        rcases x with ⟨x, hxT, hxcomp⟩
        rfl }
  have hsG_finite : sG.Finite := by
    haveI : Finite sK := hker_finite.to_subtype
    haveI : Finite sG := Finite.of_equiv _ hEquiv
    exact Set.finite_coe_iff.mp inferInstance
  refine ⟨by simpa [sG] using hsG_finite, ?_⟩
  have hcard_eq : Set.ncard sG = Set.ncard sK := (Set.ncard_congr' hEquiv).symm
  calc
    Set.ncard {x : G | (n : ℕ) • x = 0 ∧ component x = 0}
        = Set.ncard sG := rfl
    _ = Set.ncard sK := hcard_eq
    _ = Set.ncard {x : component.ker | (n : ℕ) • x = 0} := rfl
    _ ≤ B := hker_card

theorem nTorsionSet_ncard_le_two_mul_of_component
    {G : Type*} [AddCommGroup G] (n : ℕ)
    (component : G →+ ZMod 2)
    (hker_finite : Set.Finite {x : G | (n : ℕ) • x = 0 ∧ component x = 0})
    (hker_card : Set.ncard {x : G | (n : ℕ) • x = 0 ∧ component x = 0} ≤ n) :
    Set.Finite (nTorsionSet G n) ∧ Set.ncard (nTorsionSet G n) ≤ 2 * n := by
  classical
  let T : AddSubgroup G := nTorsionSubgroup G n
  let componentT : T →+ ZMod 2 := component.comp T.subtype
  have hker_equiv :
      componentT.ker ≃ {x : G // (n : ℕ) • x = 0 ∧ component x = 0} :=
    { toFun := fun x => ⟨x.1.1, by
        constructor
        · exact x.1.2
        · exact x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, by
        change component x.1 = 0
        exact x.2.2⟩
      left_inv := by
        intro x
        rcases x with ⟨⟨x, hxT⟩, hxker⟩
        rfl
      right_inv := by
        intro x
        rcases x with ⟨x, hxT, hxker⟩
        rfl }
  have hker_finite_type : Finite componentT.ker := by
    haveI : Finite {x : G // (n : ℕ) • x = 0 ∧ component x = 0} := hker_finite.to_subtype
    exact Finite.of_equiv _ hker_equiv.symm
  have hT_finite : Finite T := by
    rw [AddMonoidHom.finite_iff_finite_ker_range componentT]
    exact ⟨hker_finite_type, inferInstance⟩
  have hset_finite : Set.Finite (nTorsionSet G n) := by
    haveI : Finite T := hT_finite
    rw [show nTorsionSet G n = (T : Set G) by rfl]
    exact Set.finite_coe_iff.mp inferInstance
  refine ⟨hset_finite, ?_⟩
  have hker_card_nat :
      Nat.card componentT.ker =
        Set.ncard {x : G | (n : ℕ) • x = 0 ∧ component x = 0} := by
    calc
      Nat.card componentT.ker =
          Nat.card {x : G // (n : ℕ) • x = 0 ∧ component x = 0} :=
        Nat.card_congr hker_equiv
      _ = Set.ncard {x : G | (n : ℕ) • x = 0 ∧ component x = 0} :=
        (Nat.card_coe_set_eq _).symm
  have hrange_le : Nat.card componentT.range ≤ 2 := by
    calc
      Nat.card componentT.range = Set.ncard (componentT.range : Set (ZMod 2)) := by
        exact Nat.card_coe_set_eq _
      _ ≤ Set.ncard (Set.univ : Set (ZMod 2)) := by
        exact Set.ncard_le_ncard (Set.subset_univ _) (Set.finite_univ)
      _ = 2 := by
        simp [Set.ncard_univ, ZMod.card]
  have hcardT :
      Nat.card T = Nat.card componentT.ker * Nat.card componentT.range := by
    rw [← componentT.ker.card_mul_index, AddSubgroup.index_ker]
  rw [show Set.ncard (nTorsionSet G n) = Nat.card T by
    rw [show nTorsionSet G n = (T : Set G) by rfl]
    exact (Nat.card_coe_set_eq _).symm]
  rw [hcardT, hker_card_nat]
  nlinarith

theorem nTorsionSet_ncard_le_two_mul_of_component_ker
    {G : Type*} [AddCommGroup G] (n : ℕ)
    (component : G →+ ZMod 2)
    (hker_finite : Set.Finite {x : component.ker | (n : ℕ) • x = 0})
    (hker_card : Set.ncard {x : component.ker | (n : ℕ) • x = 0} ≤ n) :
    Set.Finite (nTorsionSet G n) ∧ Set.ncard (nTorsionSet G n) ≤ 2 * n := by
  rcases component_ker_nTorsionSet_to_ambient component n n hker_finite hker_card with
    ⟨hfin, hcard⟩
  exact nTorsionSet_ncard_le_two_mul_of_component n component hfin hcard

theorem nTorsionSet_ncard_le_two_mul_of_component_theta
    {G : Type*} [AddCommGroup G] (n : ℕ) (hn : 0 < n)
    (component : G →+ ZMod 2) {T : ℝ}
    (theta : component.ker →+ AddCircle T)
    (htheta : Function.Injective theta) :
    Set.Finite (nTorsionSet G n) ∧ Set.ncard (nTorsionSet G n) ≤ 2 * n := by
  obtain ⟨hker_finite, hker_card⟩ :=
    nTorsionSet_ncard_le_of_injective_addCircle theta htheta n hn
  exact nTorsionSet_ncard_le_two_mul_of_component_ker n component hker_finite hker_card

theorem shortW_nTorsionSet_ncard_le_of_componentTheta
    {A B e T : ℝ}
    (hroot : RealTopology.shortCubic A B e = 0)
    (hderiv : 0 < RealTopology.shortCubicDeriv A B e)
    (theta :
      (RealTopology.componentBitHom (A := A) (B := B) (e := e) hroot hderiv).ker →+
        AddCircle T)
    (htheta : Function.Injective theta)
    (n : ℕ) (hn : 0 < n) :
    Set.Finite
        {P : WeierstrassCurve.Affine.Point (RealTopology.shortW A B) |
          (n : ℕ) • P = 0} ∧
      Set.ncard
        {P : WeierstrassCurve.Affine.Point (RealTopology.shortW A B) |
          (n : ℕ) • P = 0} ≤ 2 * n := by
  simpa [nTorsionSet] using
    nTorsionSet_ncard_le_two_mul_of_component_theta
      (G := WeierstrassCurve.Affine.Point (RealTopology.shortW A B))
      n hn (RealTopology.componentBitHom (A := A) (B := B) (e := e) hroot hderiv)
      theta htheta

theorem shortW_nTorsionSet_ncard_le_of_componentKer_embeds_addCircle
    {A B e : ℝ}
    (hroot : RealTopology.shortCubic A B e = 0)
    (hderiv : 0 < RealTopology.shortCubicDeriv A B e)
    (hembed :
      ∃ T : ℝ,
        ∃ theta :
          (RealTopology.componentBitHom (A := A) (B := B) (e := e) hroot hderiv).ker →+
            AddCircle T,
          Function.Injective theta)
    (n : ℕ) (hn : 0 < n) :
    Set.Finite
        {P : WeierstrassCurve.Affine.Point (RealTopology.shortW A B) |
          (n : ℕ) • P = 0} ∧
      Set.ncard
        {P : WeierstrassCurve.Affine.Point (RealTopology.shortW A B) |
          (n : ℕ) • P = 0} ≤ 2 * n := by
  rcases hembed with ⟨T, theta, htheta⟩
  exact shortW_nTorsionSet_ncard_le_of_componentTheta hroot hderiv theta htheta n hn

private theorem sq_le_two_mul_of_pos {m : ℕ} (hm : 0 < m) (h : m * m ≤ 2 * m) :
    m ≤ 2 := by
  nlinarith

/-! ## The hard real-topology input

This is the single Day 0 interface for the Fable 5 route.  The intended proof
is: show `E(ℝ)` has identity component isomorphic to an additive circle and
component group of order at most two, then count `n`-torsion.
-/
theorem card_E_R_torsion_le
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (n : ℕ) (hn : 0 < n) :
    Set.Finite {P : (E⁄ℝ).Point | (n : ℕ) • P = 0} ∧
      Set.ncard {P : (E⁄ℝ).Point | (n : ℕ) • P = 0} ≤ 2 * n := by
  sorry

/-! ## Assembly -/

theorem fullRationalTorsion_order_le_two_route4B
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    m ≤ 2 := by
  apply sq_le_two_mul_of_pos hm
  obtain ⟨f, hf⟩ := hfull
  haveI : NeZero m := ⟨by omega⟩
  -- The base change ℚ → ℝ gives an injective group hom on points
  let bc : (E⁄ℚ).Point →+ (E⁄ℝ).Point :=
    WeierstrassCurve.Affine.Point.baseChange ℚ ℝ
  have hbc_inj : Function.Injective bc :=
    WeierstrassCurve.Affine.Point.map_injective (Algebra.ofId ℚ ℝ)
  -- Compose: (ℤ/m)² →+ E(ℚ) →+ E(ℝ), injective
  let g : ZMod m × ZMod m →+ (E⁄ℝ).Point := bc.comp f
  have hg_inj : Function.Injective g := hbc_inj.comp hf
  -- Every element of (ℤ/m)² has order dividing m, so maps into E(ℝ)[m]
  have hg_torsion : ∀ x : ZMod m × ZMod m, (m : ℕ) • g x = 0 := by
    intro x
    simp only [g, AddMonoidHom.comp_apply, ← map_nsmul]
    have : (m : ℕ) • x = 0 := by
      ext <;> exact ZModModule.char_nsmul_eq_zero m _
    rw [this, map_zero, map_zero]
  -- Image ⊆ torsion set
  have himage_sub : Set.range g ⊆ {P : (E⁄ℝ).Point | (m : ℕ) • P = 0} := by
    rintro _ ⟨x, rfl⟩
    exact hg_torsion x
  obtain ⟨htors_finite, htors_card⟩ := card_E_R_torsion_le E m hm
  -- Chain: m² = ncard(image) ≤ ncard(torsion) ≤ 2m
  calc m * m
      = Nat.card (ZMod m × ZMod m) := by
          simp [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card]
    _ = (Set.range g).ncard := (Set.ncard_range_of_injective hg_inj).symm
    _ ≤ Set.ncard {P : (E⁄ℝ).Point | (m : ℕ) • P = 0} :=
        Set.ncard_le_ncard himage_sub htors_finite
    _ ≤ 2 * m := htors_card

end MazurProof
