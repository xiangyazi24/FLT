import Mathlib
import FLT.Assumptions.MazurProof.RealTopologyS3
import FLT.Assumptions.MazurProof.RealTopologyS11Assembly
import FLT.Assumptions.MazurProof.TorsionDefs

/-!
# Route 4B: fullRationalTorsion_order_le_two via real torsion bound

E(ℚ)[m] ↪ E(ℝ)[m] via base change (Mathlib's Point.baseChange).
E(ℝ) is a compact 1-dim real Lie group with ≤ 2 components → #E(ℝ)[m] ≤ 2m.
(ℤ/m)² ↪ E(ℚ) gives m² ≤ 2m → m ≤ 2.
-/

open scoped WeierstrassCurve.Affine

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : Affine F) [W.IsElliptic]
variable (r s t : F)

private abbrev vc : VariableChange F := ⟨1, r, s, t⟩
private abbrev W' : Affine F := vc r s t • W

private theorem equation_vc (x y : F) :
    W.Equation x y ↔ (W' W r s t).Equation (x - r) (y - s * (x - r) - t) := by
  simp only [equation_iff, W', vc, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, inv_one, one_pow, Units.val_one, one_mul]
  constructor <;> intro h <;> linear_combination h

private theorem nonsingular_vc {x y : F} (h : W.Nonsingular x y) :
    (W' W r s t).Nonsingular (x - r) (y - s * (x - r) - t) :=
  equation_iff_nonsingular.mp ((equation_vc W r s t x y).mp h.1)

private theorem negY_vc (x y : F) :
    (W' W r s t).negY (x - r) (y - s * (x - r) - t) =
    W.negY x y - s * (x - r) - t := by
  simp only [negY, W', vc, variableChange_a₁, variableChange_a₃, inv_one, one_pow,
    Units.val_one, one_mul]
  ring

private theorem addX_vc (x₁ x₂ ℓ : F) :
    (W' W r s t).addX (x₁ - r) (x₂ - r) (ℓ - s) = W.addX x₁ x₂ ℓ - r := by
  simp only [addX, W', vc, variableChange_a₁, variableChange_a₂, inv_one, one_pow,
    Units.val_one, one_mul]
  ring

private theorem addY_vc (x₁ x₂ y₁ ℓ : F) :
    (W' W r s t).addY (x₁ - r) (x₂ - r) (y₁ - s * (x₁ - r) - t) (ℓ - s) =
    W.addY x₁ x₂ y₁ ℓ - s * (W.addX x₁ x₂ ℓ - r) - t := by
  simp only [addY, negY, negAddY, addX, W', vc, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, inv_one, one_pow, Units.val_one, one_mul]
  ring

private theorem slope_vc_of_X_ne {x₁ x₂ y₁ y₂ : F} (hx : x₁ ≠ x₂) :
    (W' W r s t).slope (x₁ - r) (x₂ - r)
      (y₁ - s * (x₁ - r) - t) (y₂ - s * (x₂ - r) - t) =
    W.slope x₁ x₂ y₁ y₂ - s := by
  have hx' : x₁ - r ≠ x₂ - r := by
    intro h
    exact hx (show x₁ = x₂ by linear_combination h)
  rw [slope_of_X_ne hx', slope_of_X_ne hx]
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  field_simp [hd]
  ring

private theorem slope_vc_of_Y_ne {x₁ y₁ y₂ : F}
    (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₁ y₂)
    (hy : y₁ ≠ W.negY x₁ y₂) :
    (W' W r s t).slope (x₁ - r) (x₁ - r)
      (y₁ - s * (x₁ - r) - t) (y₂ - s * (x₁ - r) - t) =
    W.slope x₁ x₁ y₁ y₂ - s := by
  have heq : y₁ = y₂ := (Y_eq_of_X_eq h₁.1 h₂.1 rfl).resolve_right hy
  have hne : y₁ ≠ W.negY x₁ y₁ := by
    rwa [show W.negY x₁ y₁ = W.negY x₁ y₂ from by rw [heq]]
  have hy' : y₁ - s * (x₁ - r) - t ≠
      (W' W r s t).negY (x₁ - r) (y₂ - s * (x₁ - r) - t) := by
    rw [negY_vc]
    intro h
    exact hy (show y₁ = W.negY x₁ y₂ by
      simp only [negY] at h ⊢
      linear_combination h)
  rw [slope_of_Y_ne rfl hy', slope_of_Y_ne rfl hy]
  simp only [negY, W', vc, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, inv_one, one_pow, Units.val_one, one_mul]
  have hd : y₁ - (-y₁ - W.a₁ * x₁ - W.a₃) ≠ 0 := by
    intro h
    exact hne (show y₁ = W.negY x₁ y₁ by
      simp only [negY]
      linear_combination h)
  ring_nf at hd ⊢
  field_simp [hd]
  ring

private theorem slope_vc {x₁ x₂ y₁ y₂ : F}
    (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    (W' W r s t).slope (x₁ - r) (x₂ - r)
      (y₁ - s * (x₁ - r) - t) (y₂ - s * (x₂ - r) - t) =
    W.slope x₁ x₂ y₁ y₂ - s := by
  by_cases hx : x₁ = x₂
  · subst hx
    exact slope_vc_of_Y_ne W r s t h₁ h₂ (fun h => hxy ⟨rfl, h⟩)
  · exact slope_vc_of_X_ne W r s t hx

private noncomputable def vcPointFun :
    W.Point → (W' W r s t).Point
  | .zero => .zero
  | .some _ _ h => .some _ _ (nonsingular_vc W r s t h)

@[simp]
private theorem vcPointFun_zero :
    vcPointFun W r s t (0 : W.Point) = 0 := rfl

@[simp]
private theorem vcPointFun_some {x y : F} (h : W.Nonsingular x y) :
    vcPointFun W r s t (.some x y h) =
    Point.some (x - r) (y - s * (x - r) - t) (nonsingular_vc W r s t h) := rfl

private theorem vcPointFun_add (P Q : W.Point) :
    vcPointFun W r s t (P + Q) =
    vcPointFun W r s t P + vcPointFun W r s t Q := by
  match P, Q with
  | .zero, _ => rfl
  | _, .zero =>
      show vcPointFun W r s t (_ + 0) = vcPointFun W r s t _ + vcPointFun W r s t 0
      rw [add_zero, vcPointFun_zero, add_zero]
  | Point.some x₁ y₁ h₁, Point.some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
      · rw [Point.add_of_Y_eq hxy.1 hxy.2, vcPointFun_zero]
        simp only [vcPointFun_some]
        exact (Point.add_of_Y_eq (show x₁ - r = x₂ - r from by rw [hxy.1])
          (show y₁ - s * (x₁ - r) - t =
            (W' W r s t).negY (x₂ - r) (y₂ - s * (x₂ - r) - t) from by
            rw [negY_vc, hxy.2, hxy.1])).symm
      · have hxy' : ¬(x₁ - r = x₂ - r ∧
            y₁ - s * (x₁ - r) - t =
              (W' W r s t).negY (x₂ - r) (y₂ - s * (x₂ - r) - t)) := by
          intro ⟨hx', hy'⟩
          have hx : x₁ = x₂ := by linear_combination hx'
          subst hx
          rw [negY_vc] at hy'
          exact hxy ⟨rfl, show y₁ = W.negY x₁ y₂ by
            simp only [negY] at hy' ⊢
            linear_combination hy'⟩
        simp only [Point.add_some hxy, vcPointFun_some, Point.add_some hxy',
          Point.some.injEq]
        refine ⟨?_, ?_⟩
        · rw [slope_vc W r s t h₁ h₂ hxy, addX_vc]
        · rw [slope_vc W r s t h₁ h₂ hxy, addY_vc]

/-- The injective `AddMonoidHom` from `W.Point` to `(C • W).Point`
for a u=1 variable change `C = ⟨1, r, s, t⟩`. -/
noncomputable def variableChangePoint :
    W.Point →+ (W' W r s t).Point where
  toFun := vcPointFun W r s t
  map_zero' := rfl
  map_add' := vcPointFun_add W r s t

theorem variableChangePoint_injective :
    Function.Injective (variableChangePoint W r s t) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) heq
  · rfl
  · simp only [variableChangePoint, AddMonoidHom.coe_mk, ZeroHom.coe_mk, vcPointFun] at heq
    exact absurd heq.symm (Point.some_ne_zero _)
  · simp only [variableChangePoint, AddMonoidHom.coe_mk, ZeroHom.coe_mk, vcPointFun] at heq
    exact absurd heq (Point.some_ne_zero _)
  · simp only [variableChangePoint, AddMonoidHom.coe_mk, ZeroHom.coe_mk, vcPointFun,
      Point.some.injEq] at heq
    rw [Point.some.injEq]
    have hx : x₁ = x₂ := by linear_combination heq.1
    subst hx
    exact ⟨rfl, by linear_combination heq.2⟩

end WeierstrassCurve.Affine

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

theorem shortW_nTorsionSet_ncard_le
    {A B e : ℝ}
    (hroot : RealTopology.shortCubic A B e = 0)
    (hderiv : 0 < RealTopology.shortCubicDeriv A B e)
    (hposRight : ∀ ⦃u : ℝ⦄, e < u → 0 < RealTopology.shortCubic A B u)
    (n : ℕ) (hn : 0 < n) :
    Set.Finite
        {P : WeierstrassCurve.Affine.Point (RealTopology.shortW A B) |
          (n : ℕ) • P = 0} ∧
      Set.ncard
        {P : WeierstrassCurve.Affine.Point (RealTopology.shortW A B) |
          (n : ℕ) • P = 0} ≤ 2 * n := by
  have hadd :=
    RealTopology.thetaCandidateAdditive
      (A := A) (B := B) (e := e) hroot hderiv hposRight
  have hembed :=
    RealTopology.exists_injective_thetaHom_of_thetaCandidate_additive
      (A := A) (B := B) (e := e) hroot hderiv hposRight hadd
  exact shortW_nTorsionSet_ncard_le_of_componentKer_embeds_addCircle
    hroot hderiv hembed n hn

private theorem exists_root_monic_cubic (a b c : ℝ) :
    ∃ r : ℝ, r ^ 3 + a * r ^ 2 + b * r + c = 0 := by
  let S : ℝ := |a| + |b| + |c|
  let M : ℝ := S + 3
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    positivity
  have hMpos : 0 < M := by
    dsimp [M]
    linarith
  have hMnonneg : 0 ≤ M := hMpos.le
  let f : ℝ → ℝ := fun x => x ^ 3 + a * x ^ 2 + b * x + c
  have hpos : 0 < f M := by
    have hM2nonneg : 0 ≤ M ^ 2 := sq_nonneg M
    have ha_mul : - |a| * M ^ 2 ≤ a * M ^ 2 :=
      mul_le_mul_of_nonneg_right (neg_abs_le a) hM2nonneg
    have hb_mul : - |b| * M ≤ b * M :=
      mul_le_mul_of_nonneg_right (neg_abs_le b) hMnonneg
    have hc_le : - |c| ≤ c := neg_abs_le c
    have hlower : M ^ 3 - |a| * M ^ 2 - |b| * M - |c| ≤ f M := by
      dsimp [f]
      nlinarith
    have hlower_pos : 0 < M ^ 3 - |a| * M ^ 2 - |b| * M - |c| := by
      dsimp [M, S]
      nlinarith [abs_nonneg a, abs_nonneg b, abs_nonneg c]
    exact lt_of_lt_of_le hlower_pos hlower
  have hneg : f (-M) < 0 := by
    have hM2nonneg : 0 ≤ M ^ 2 := sq_nonneg M
    have ha_mul : a * M ^ 2 ≤ |a| * M ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self a) hM2nonneg
    have hb_mul : -b * M ≤ |b| * M := by
      have hb : -b ≤ |b| := by simpa using (neg_le_abs b)
      exact mul_le_mul_of_nonneg_right hb hMnonneg
    have hc_le : c ≤ |c| := le_abs_self c
    have hupper : f (-M) ≤ -M ^ 3 + |a| * M ^ 2 + |b| * M + |c| := by
      dsimp [f]
      nlinarith
    have hupper_neg : -M ^ 3 + |a| * M ^ 2 + |b| * M + |c| < 0 := by
      dsimp [M, S]
      nlinarith [abs_nonneg a, abs_nonneg b, abs_nonneg c]
    exact lt_of_le_of_lt hupper hupper_neg
  have hle : -M ≤ M := by linarith
  have hcont : ContinuousOn f (Set.Icc (-M) M) := by
    fun_prop
  have hzero : 0 ∈ Set.Icc (f (-M)) (f M) := ⟨hneg.le, hpos.le⟩
  rcases intermediate_value_Icc hle hcont hzero with ⟨r, _hrmem, hr⟩
  exact ⟨r, by simpa [f] using hr⟩

/-!
The algebraic geometry bridge for the real-torsion bound.  It completes the
square, translates by a real root of the resulting monic cubic, identifies the
resulting equation with `shortW A B`, and transports points by an injective
homomorphism.
-/
theorem exists_injective_shortW_model
    (W : WeierstrassCurve ℝ) [W.IsElliptic] :
    ∃ (A B : ℝ) (C : WeierstrassCurve.VariableChange ℝ),
      C.u = 1 ∧
        C • W = RealTopology.shortW A B ∧
          (RealTopology.shortW A B).IsElliptic ∧
            ∃ φ :
              WeierstrassCurve.Affine.Point W →+
                WeierstrassCurve.Affine.Point (RealTopology.shortW A B),
              Function.Injective φ := by
  let a : ℝ := W.a₂ + W.a₁ ^ 2 / 4
  let b : ℝ := W.a₄ + W.a₁ * W.a₃ / 2
  let c : ℝ := W.a₆ + W.a₃ ^ 2 / 4
  obtain ⟨r, hr⟩ := exists_root_monic_cubic a b c
  let s : ℝ := -W.a₁ / 2
  let t : ℝ := -(W.a₃ + r * W.a₁) / 2
  let C : WeierstrassCurve.VariableChange ℝ := ⟨1, r, s, t⟩
  let A : ℝ := (C • W).a₂
  let B : ℝ := (C • W).a₄
  have hmodel : C • W = RealTopology.shortW A B := by
    ext <;> simp [RealTopology.shortW, A, B, C, s, t,
      WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆]
    · ring_nf
    · ring_nf
    · dsimp [a, b, c] at hr
      ring_nf at hr ⊢
      exact hr
  have hshort : (RealTopology.shortW A B).IsElliptic := by
    rw [← hmodel]
    infer_instance
  refine ⟨A, B, C, rfl, hmodel, hshort, ?_⟩
  rw [← hmodel]
  exact ⟨WeierstrassCurve.Affine.variableChangePoint W r s t,
    WeierstrassCurve.Affine.variableChangePoint_injective W r s t⟩

theorem shortW_discriminant (A B : ℝ) :
    (RealTopology.shortW A B).Δ = 16 * B ^ 2 * (A ^ 2 - 4 * B) := by
  simp [RealTopology.shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem shortW_B_ne_zero_of_isElliptic
    {A B : ℝ} [(RealTopology.shortW A B).IsElliptic] :
    B ≠ 0 := by
  have hΔunit : IsUnit (RealTopology.shortW A B).Δ :=
    WeierstrassCurve.IsElliptic.isUnit
  have hΔ : (RealTopology.shortW A B).Δ ≠ 0 := hΔunit.ne_zero
  intro hB
  apply hΔ
  rw [shortW_discriminant, hB]
  ring

theorem shortW_quadratic_discriminant_ne_zero_of_isElliptic
    {A B : ℝ} [(RealTopology.shortW A B).IsElliptic] :
    A ^ 2 - 4 * B ≠ 0 := by
  have hΔunit : IsUnit (RealTopology.shortW A B).Δ :=
    WeierstrassCurve.IsElliptic.isUnit
  have hΔ : (RealTopology.shortW A B).Δ ≠ 0 := hΔunit.ne_zero
  intro hdisc
  apply hΔ
  rw [shortW_discriminant, hdisc]
  ring

private theorem shortCubic_quadratic_factor_pos
    {A B u : ℝ} (hDpos : 0 < A ^ 2 - 4 * B) :
    RealTopology.shortCubic A B u =
      u * (u - (-A - Real.sqrt (A ^ 2 - 4 * B)) / 2) *
        (u - (-A + Real.sqrt (A ^ 2 - 4 * B)) / 2) := by
  have hDpos' : 0 < A ^ 2 - B * 4 := by nlinarith
  have hsq : (Real.sqrt (A ^ 2 - B * 4)) ^ 2 = A ^ 2 - B * 4 :=
    Real.sq_sqrt hDpos'.le
  rw [RealTopology.shortCubic]
  ring_nf
  rw [hsq]
  ring

private theorem shortCubicDeriv_upperRoot_eq
    {A B : ℝ} (hDpos : 0 < A ^ 2 - 4 * B) :
    RealTopology.shortCubicDeriv A B ((-A + Real.sqrt (A ^ 2 - 4 * B)) / 2) =
      ((-A + Real.sqrt (A ^ 2 - 4 * B)) / 2) *
        (((-A + Real.sqrt (A ^ 2 - 4 * B)) / 2) -
          ((-A - Real.sqrt (A ^ 2 - 4 * B)) / 2)) := by
  have hDpos' : 0 < A ^ 2 - B * 4 := by nlinarith
  have hsq : (Real.sqrt (A ^ 2 - B * 4)) ^ 2 = A ^ 2 - B * 4 :=
    Real.sq_sqrt hDpos'.le
  rw [RealTopology.shortCubicDeriv]
  ring_nf
  rw [hsq]
  ring

private theorem shortCubic_B_eq_roots_product
    {A B : ℝ} (hDpos : 0 < A ^ 2 - 4 * B) :
    B =
      ((-A - Real.sqrt (A ^ 2 - 4 * B)) / 2) *
        ((-A + Real.sqrt (A ^ 2 - 4 * B)) / 2) := by
  have hDpos' : 0 < A ^ 2 - B * 4 := by nlinarith
  have hsq : (Real.sqrt (A ^ 2 - B * 4)) ^ 2 = A ^ 2 - B * 4 :=
    Real.sq_sqrt hDpos'.le
  ring_nf
  rw [hsq]
  ring

private theorem exists_shortCubic_right_root_of_negative_discriminant
    {A B : ℝ} (hDneg : A ^ 2 - 4 * B < 0) :
    ∃ e : ℝ,
      RealTopology.shortCubic A B e = 0 ∧
        0 < RealTopology.shortCubicDeriv A B e ∧
        (∀ ⦃u : ℝ⦄, e < u → 0 < RealTopology.shortCubic A B u) := by
  refine ⟨0, ?_, ?_, ?_⟩
  · simp [RealTopology.shortCubic]
  · have hBpos : 0 < B := by
      have hsq : 0 ≤ A ^ 2 := sq_nonneg A
      nlinarith
    simpa [RealTopology.shortCubicDeriv] using hBpos
  · intro u hu
    have hq : 0 < u ^ 2 + A * u + B := by
      have hDpos : 0 < 4 * B - A ^ 2 := by nlinarith
      have hs : 0 ≤ (2 * u + A) ^ 2 := sq_nonneg (2 * u + A)
      have hsum : 0 < (2 * u + A) ^ 2 + (4 * B - A ^ 2) :=
        add_pos_of_nonneg_of_pos hs hDpos
      nlinarith
    have hmul : 0 < u * (u ^ 2 + A * u + B) := mul_pos hu hq
    rw [RealTopology.shortCubic]
    nlinarith

private theorem exists_shortCubic_right_root_of_positive_discriminant
    {A B : ℝ} (hB : B ≠ 0) (hDpos : 0 < A ^ 2 - 4 * B) :
    ∃ e : ℝ,
      RealTopology.shortCubic A B e = 0 ∧
        0 < RealTopology.shortCubicDeriv A B e ∧
        (∀ ⦃u : ℝ⦄, e < u → 0 < RealTopology.shortCubic A B u) := by
  let r₁ := (-A - Real.sqrt (A ^ 2 - 4 * B)) / 2
  let r₂ := (-A + Real.sqrt (A ^ 2 - 4 * B)) / 2
  have hspos : 0 < Real.sqrt (A ^ 2 - 4 * B) := Real.sqrt_pos.2 hDpos
  have hr12 : r₁ < r₂ := by
    dsimp [r₁, r₂]
    linarith
  by_cases hr2pos : 0 < r₂
  · refine ⟨r₂, ?_, ?_, ?_⟩
    · rw [shortCubic_quadratic_factor_pos (A := A) (B := B) (u := r₂) hDpos]
      ring
    · rw [show r₂ = (-A + Real.sqrt (A ^ 2 - 4 * B)) / 2 by rfl]
      rw [shortCubicDeriv_upperRoot_eq (A := A) (B := B) hDpos]
      dsimp [r₁, r₂] at hr12 hr2pos ⊢
      exact mul_pos hr2pos (sub_pos.mpr hr12)
    · intro u hu
      rw [shortCubic_quadratic_factor_pos (A := A) (B := B) (u := u) hDpos]
      have hu0 : 0 < u := lt_trans hr2pos hu
      have hur1 : 0 < u - r₁ := by linarith
      have hur2 : 0 < u - r₂ := sub_pos.mpr hu
      dsimp [r₁, r₂] at hur1 hur2
      positivity
  · have hr2le : r₂ ≤ 0 := not_lt.mp hr2pos
    have hr2ne : r₂ ≠ 0 := by
      intro hr2zero
      apply hB
      have hsq : (Real.sqrt (A ^ 2 - 4 * B)) ^ 2 = A ^ 2 - 4 * B :=
        Real.sq_sqrt hDpos.le
      dsimp [r₂] at hr2zero
      nlinarith
    have hr2neg : r₂ < 0 := lt_of_le_of_ne hr2le hr2ne
    have hr1neg : r₁ < 0 := lt_trans hr12 hr2neg
    have hBpos : 0 < B := by
      rw [shortCubic_B_eq_roots_product (A := A) (B := B) hDpos]
      dsimp [r₁, r₂] at hr1neg hr2neg
      exact mul_pos_of_neg_of_neg hr1neg hr2neg
    refine ⟨0, ?_, ?_, ?_⟩
    · simp [RealTopology.shortCubic]
    · simpa [RealTopology.shortCubicDeriv] using hBpos
    · intro u hu
      rw [shortCubic_quadratic_factor_pos (A := A) (B := B) (u := u) hDpos]
      have hur1 : 0 < u - r₁ := by linarith
      have hur2 : 0 < u - r₂ := by linarith
      dsimp [r₁, r₂] at hur1 hur2
      positivity

/-!
The remaining real-root bridge for `shortW`.  The intended proof chooses the
largest real root of `x^3 + A*x^2 + B*x`; ellipticity excludes multiple roots,
so the derivative is positive there and the cubic is positive to the right.
-/
theorem exists_shortCubic_right_root_of_simple
    {A B : ℝ} (hB : B ≠ 0) (hdisc : A ^ 2 - 4 * B ≠ 0) :
    ∃ e : ℝ,
      RealTopology.shortCubic A B e = 0 ∧
        0 < RealTopology.shortCubicDeriv A B e ∧
        (∀ ⦃u : ℝ⦄, e < u → 0 < RealTopology.shortCubic A B u) := by
  rcases lt_or_gt_of_ne hdisc with hDneg | hDpos
  · exact exists_shortCubic_right_root_of_negative_discriminant hDneg
  · exact exists_shortCubic_right_root_of_positive_discriminant hB hDpos

theorem exists_shortCubic_right_root
    {A B : ℝ} [(RealTopology.shortW A B).IsElliptic] :
    ∃ e : ℝ,
      RealTopology.shortCubic A B e = 0 ∧
        0 < RealTopology.shortCubicDeriv A B e ∧
        (∀ ⦃u : ℝ⦄, e < u → 0 < RealTopology.shortCubic A B u) := by
  exact exists_shortCubic_right_root_of_simple
    (shortW_B_ne_zero_of_isElliptic (A := A) (B := B))
    (shortW_quadratic_discriminant_ne_zero_of_isElliptic (A := A) (B := B))

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
  haveI : (E⁄ℝ).IsElliptic := by
    change (E.map (algebraMap ℚ ℝ)).IsElliptic
    infer_instance
  obtain ⟨A, B, C, hCu, hmodel, hshort, φ, hφ⟩ :=
    exists_injective_shortW_model (E⁄ℝ)
  haveI : (RealTopology.shortW A B).IsElliptic := hshort
  obtain ⟨e, hroot, hderiv, hposRight⟩ :=
    exists_shortCubic_right_root (A := A) (B := B)
  obtain ⟨hshort_finite, hshort_card⟩ :=
    shortW_nTorsionSet_ncard_le hroot hderiv hposRight n hn
  exact nTorsionSet_ncard_le_of_injective_addMonoidHom
    φ hφ n (2 * n) hshort_finite hshort_card

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
