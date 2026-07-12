import FLT.Assumptions.MazurProof.N18RouteC_LocalThreeSound
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Unit cube classes in the N18 cubic field

Dirichlet's theorem gives two free unit directions.  The finite `pi^5`
calculation proves that the concrete units `a` and `a+1` are independent
modulo cubes; cardinality then shows that they generate every unit cube
class.
-/

namespace MazurProof.N18RouteC.UnitCubes

open FieldArithmetic LocalThree LocalThreeSound
open scoped NumberField

noncomputable section

abbrev OL := NumberField.RingOfIntegers L
abbrev U := OLˣ
abbrev UQ := U ⧸ NumberField.Units.torsion L
abbrev FundIndex := Fin (NumberField.Units.rank L)

local instance quotientIntModule : Module ℤ (Additive UQ) :=
  AddCommGroup.toIntModule (Additive UQ)

def unitExponent (u : U) (i : FundIndex) : ℤ :=
  (NumberField.Units.basisModTorsion L).repr
    (Additive.ofMul (QuotientGroup.mk u : UQ)) i

def cubeResidue (u : U) (i : FundIndex) : ZMod 3 := unitExponent u i

theorem unitExponent_mul (u v : U) (i : FundIndex) :
    unitExponent (u * v) i = unitExponent u i + unitExponent v i := by
  simp [unitExponent, QuotientGroup.mk_mul, ofMul_mul]

theorem unitExponent_inv (u : U) (i : FundIndex) :
    unitExponent u⁻¹ i = -unitExponent u i := by
  simp only [unitExponent, QuotientGroup.mk_inv, ofMul_inv]
  exact congrArg (fun f : FundIndex →₀ ℤ ↦ f i)
    ((NumberField.Units.basisModTorsion L).repr.map_neg
      (Additive.ofMul (QuotientGroup.mk u : UQ)))

theorem unitExponent_pow (u : U) (n : ℕ) (i : FundIndex) :
    unitExponent (u ^ n) i = n * unitExponent u i := by
  induction n with
  | zero => simp [unitExponent]
  | succ n ih =>
      rw [pow_succ, unitExponent_mul, ih]
      push_cast
      ring

theorem cubeResidue_mul (u v : U) :
    cubeResidue (u * v) = cubeResidue u + cubeResidue v := by
  funext i
  simp [cubeResidue, unitExponent_mul]

theorem cubeResidue_inv (u : U) :
    cubeResidue u⁻¹ = -cubeResidue u := by
  funext i
  simp [cubeResidue, unitExponent_inv]

theorem cubeResidue_pow (u : U) (n : ℕ) :
    cubeResidue (u ^ n) = n • cubeResidue u := by
  funext i
  simp [cubeResidue, unitExponent_pow, nsmul_eq_mul]

private theorem torsion_cube (z : NumberField.Units.torsion L) :
    ∃ e : U, (z : U) = e ^ 3 := by
  have hodd : Odd (Module.finrank ℚ L) := by
    rw [finrank_L]
    norm_num [Odd]
  rcases NumberField.Units.torsion_eq_one_or_neg_one_of_odd_finrank
      (K := L) hodd z with hz | hz
  · exact ⟨1, by simpa using hz⟩
  · refine ⟨-1, hz.trans ?_⟩
    apply Units.ext
    norm_num

theorem isCube_of_cubeResidue_eq_zero (u : U)
    (hu : cubeResidue u = 0) :
    ∃ v : U, u = v ^ 3 := by
  let b := NumberField.Units.basisModTorsion L
  let c := b.repr (Additive.ofMul (QuotientGroup.mk u : UQ))
  have hcdiv : ∀ i : FundIndex, (3 : ℤ) ∣ c i := by
    intro i
    have hi : ((c i : ℤ) : ZMod 3) = 0 := by
      simpa [cubeResidue, unitExponent, c, b] using congrFun hu i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (c i) 3).mp hi
  let d : FundIndex →₀ ℤ :=
    Finsupp.mapRange (fun z : ℤ ↦ z / 3) (by simp) c
  have hthree_d : (3 : ℤ) • d = c := by
    ext i
    simp only [Finsupp.smul_apply, d, Finsupp.mapRange_apply,
      smul_eq_mul]
    exact Int.mul_ediv_cancel' (hcdiv i)
  let q : Additive UQ := b.repr.symm d
  have hq : (3 : ℤ) • q =
      Additive.ofMul (QuotientGroup.mk u : UQ) := by
    apply b.repr.injective
    simpa only [map_smul, LinearEquiv.apply_symm_apply, q, c] using hthree_d
  obtain ⟨v, hv⟩ := QuotientGroup.mk'_surjective
    (NumberField.Units.torsion L) (Additive.toMul q)
  have hv3 : (QuotientGroup.mk (v ^ 3) : UQ) = QuotientGroup.mk u := by
    calc
      (QuotientGroup.mk (v ^ 3) : UQ) =
          (QuotientGroup.mk v : UQ) ^ 3 := by simp
      _ = Additive.toMul q ^ 3 := congrArg (fun x : UQ ↦ x ^ 3) hv
      _ = Additive.toMul ((3 : ℤ) • q) := rfl
      _ = Additive.toMul (Additive.ofMul (QuotientGroup.mk u : UQ)) := by
        rw [hq]
      _ = QuotientGroup.mk u := by simp
  let z : U := u * (v ^ 3)⁻¹
  have hzmem : z ∈ NumberField.Units.torsion L := by
    rw [← QuotientGroup.eq_one_iff]
    simp [z, hv3]
  obtain ⟨e, he⟩ := torsion_cube ⟨z, hzmem⟩
  change z = e ^ 3 at he
  refine ⟨e * v, ?_⟩
  calc
    u = z * v ^ 3 := by simp [z]
    _ = e ^ 3 * v ^ 3 := by rw [he]
    _ = (e * v) ^ 3 := by simp [mul_pow]

def generatorResidue (p : F3 × F3) (r : FundIndex) : ZMod 3 :=
  (p.1.val : ZMod 3) * cubeResidue aUnit r +
    (p.2.val : ZMod 3) * cubeResidue aplusUnit r

private theorem residue_generators (i j : F3) :
    cubeResidue (aUnit ^ i.val * aplusUnit ^ j.val) =
      generatorResidue (i, j) := by
  funext r
  simp [generatorResidue, cubeResidue_mul, cubeResidue_pow,
    nsmul_eq_mul]

def sub3 (x y : F3) : F3 :=
  ⟨(x.val + 3 - y.val) % 3, Nat.mod_lt _ (by omega)⟩

private theorem sub3_cast (x y : F3) :
    ((sub3 x y).val : ZMod 3) =
      (x.val : ZMod 3) - (y.val : ZMod 3) := by
  native_decide +revert

private theorem sub3_eq_zero_iff (x y : F3) :
    sub3 x y = 0 ↔ x = y := by
  native_decide +revert

theorem generatorResidue_injective : Function.Injective generatorResidue := by
  rintro ⟨p1, p2⟩ ⟨q1, q2⟩ hpq
  let i : F3 := sub3 p1 q1
  let j : F3 := sub3 p2 q2
  let w : U := aUnit ^ i.val * aplusUnit ^ j.val
  have hwres : cubeResidue w = 0 := by
    rw [residue_generators]
    funext r
    have hr := congrFun hpq r
    dsimp [generatorResidue, i, j] at hr ⊢
    rw [sub3_cast, sub3_cast]
    linear_combination hr
  obtain ⟨v, hv⟩ := isCube_of_cubeResidue_eq_zero w hwres
  have hvL := congrArg (fun e : U ↦ (((e : OL) : L))) hv
  have hij : i = 0 ∧ j = 0 := by
    apply a_aplus_independent_mod_cube i j v
    simpa [w] using hvL
  apply Prod.ext
  · exact (sub3_eq_zero_iff p1 q1).mp (by simpa [i] using hij.1)
  · exact (sub3_eq_zero_iff p2 q2).mp (by simpa [j] using hij.2)

theorem generatorResidue_surjective : Function.Surjective generatorResidue := by
  exact ((Fintype.bijective_iff_injective_and_card generatorResidue).mpr
    ⟨generatorResidue_injective, by simp [unitRank_eq_two]⟩).surjective

theorem unit_cubeclass_classification (u : U) :
    ∃ i j : F3, ∃ v : U,
      u = aUnit ^ i.val * aplusUnit ^ j.val * v ^ 3 := by
  obtain ⟨⟨i, j⟩, hij⟩ := generatorResidue_surjective (cubeResidue u)
  let g : U := aUnit ^ i.val * aplusUnit ^ j.val
  let w : U := g⁻¹ * u
  have hwres : cubeResidue w = 0 := by
    rw [cubeResidue_mul, cubeResidue_inv]
    rw [show cubeResidue g = generatorResidue (i, j) by
      simpa [g] using residue_generators i j]
    rw [hij]
    simp
  obtain ⟨v, hv⟩ := isCube_of_cubeResidue_eq_zero w hwres
  refine ⟨i, j, v, ?_⟩
  calc
    u = g * w := by dsimp [w]; group
    _ = g * v ^ 3 := by rw [hv]
    _ = aUnit ^ i.val * aplusUnit ^ j.val * v ^ 3 := rfl

end

end MazurProof.N18RouteC.UnitCubes
