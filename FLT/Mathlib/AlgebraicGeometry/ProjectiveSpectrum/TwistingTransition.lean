import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Transition units for twists on degree-one projective charts

Let `f` and `g` be homogeneous elements of degree one.  On the overlap
`D₊(f) ∩ D₊(g) = D₊(fg)`, the fraction `g/f` has degree zero and is a unit.
This file constructs that unit directly in Mathlib's
`HomogeneousLocalization.Away` and proves its inverse and triple-overlap
cocycle identities.

For a negatively shifted graded module `A(-d)`, changing from the
`f`-trivialization to the `g`-trivialization multiplies by `(g/f)^d`.
`negativeTwistTransition` packages this multiplication as a linear
equivalence.  These are the algebraic transition data required to glue the
projective twisting sheaf on a degree-one affine cover.
-/

noncomputable section

open DirectSum
open Graded
open CategoryTheory

universe u

namespace HomogeneousLocalization.Away

variable {A σ : Type u} [CommRing A] [SetLike σ A]
variable [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- On the overlap of two degree-one projective charts, this homogeneous
fraction represents the transition ratio `g/f`.  The numerator `g²` and
denominator `fg` have the same degree. -/
def degreeOneRatio {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) :
    HomogeneousLocalization.Away 𝒜 (f * g) :=
  HomogeneousLocalization.Away.mk 𝒜 (SetLike.mul_mem_graded hf hg) 1
    (g ^ 2) (by simpa using SetLike.pow_mem_graded 2 hg)

/-- The reverse ratio `f/g`, represented in the same overlap ring. -/
def degreeOneRatioInv {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) :
    HomogeneousLocalization.Away 𝒜 (f * g) :=
  HomogeneousLocalization.Away.mk 𝒜 (SetLike.mul_mem_graded hf hg) 1
    (f ^ 2) (by simpa using SetLike.pow_mem_graded 2 hf)

/-- The two chart ratios are inverse in the overlap ring. -/
theorem degreeOneRatio_mul_inv {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) :
    degreeOneRatio 𝒜 hf hg * degreeOneRatioInv 𝒜 hf hg = 1 := by
  ext
  simp only [degreeOneRatio, degreeOneRatioInv,
    HomogeneousLocalization.val_mul, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul, HomogeneousLocalization.val_one]
  rw [← Localization.mk_one]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp
  ring

/-- The chart ratio as a unit of the overlap ring. -/
def degreeOneRatioUnit {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) :
    (HomogeneousLocalization.Away 𝒜 (f * g))ˣ where
  val := degreeOneRatio 𝒜 hf hg
  inv := degreeOneRatioInv 𝒜 hf hg
  val_inv := degreeOneRatio_mul_inv 𝒜 hf hg
  inv_val := by
    calc
      degreeOneRatioInv 𝒜 hf hg * degreeOneRatio 𝒜 hf hg =
          degreeOneRatio 𝒜 hf hg * degreeOneRatioInv 𝒜 hf hg := mul_comm _ _
      _ = 1 := degreeOneRatio_mul_inv 𝒜 hf hg

/-- Changing from the `f`-trivialization to the `g`-trivialization of the
negative twist by `debt` multiplies by `(g/f)^debt`. -/
def negativeTwistTransition {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (debt : ℕ) :
    HomogeneousLocalization.Away 𝒜 (f * g) ≃ₗ[HomogeneousLocalization.Away 𝒜 (f * g)]
      HomogeneousLocalization.Away 𝒜 (f * g) :=
  DistribMulAction.toLinearEquiv (HomogeneousLocalization.Away 𝒜 (f * g))
    (HomogeneousLocalization.Away 𝒜 (f * g)) ((degreeOneRatioUnit 𝒜 hf hg) ^ debt)

/-- A positive twist uses the inverse chart ratio: changing from the
`f`-trivialization to the `g`-trivialization multiplies by `(f/g)^credit`. -/
def positiveTwistTransition {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (credit : ℕ) :
    HomogeneousLocalization.Away 𝒜 (f * g) ≃ₗ[HomogeneousLocalization.Away 𝒜 (f * g)]
      HomogeneousLocalization.Away 𝒜 (f * g) :=
  DistribMulAction.toLinearEquiv (HomogeneousLocalization.Away 𝒜 (f * g))
    (HomogeneousLocalization.Away 𝒜 (f * g))
    (((degreeOneRatioUnit 𝒜 hf hg)⁻¹) ^ credit)

/-- Tensoring two negative twists adds their degree debts. -/
theorem negativeTwistTransition_add {f g : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (a b : ℕ) :
    (negativeTwistTransition 𝒜 hf hg a).trans
        (negativeTwistTransition 𝒜 hf hg b) =
      negativeTwistTransition 𝒜 hf hg (a + b) := by
  apply LinearEquiv.ext
  intro x
  change ((degreeOneRatioUnit 𝒜 hf hg) ^ b) •
      ((degreeOneRatioUnit 𝒜 hf hg) ^ a) • x =
    ((degreeOneRatioUnit 𝒜 hf hg) ^ (a + b)) • x
  rw [← mul_smul, ← pow_add, add_comm]

/-- For equations of degrees two and three, the product of the two conormal
transition factors is the negative-twist factor of degree five. -/
theorem degreeTwoThreeDetTransition {f g : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) :
    (degreeOneRatioUnit 𝒜 hf hg) ^ 2 *
        (degreeOneRatioUnit 𝒜 hf hg) ^ 3 =
      (degreeOneRatioUnit 𝒜 hf hg) ^ 5 := by
  rw [← pow_add]

/-- The local transition calculation behind adjunction for a `(2,3)`
complete intersection in projective three-space:
`O(-4) ⊗ det(O(-2) ⊕ O(-3))⁻¹ = O(1)`. -/
theorem degreeTwoThreeAdjunctionTransition {f g : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) :
    (negativeTwistTransition 𝒜 hf hg 4).trans
        (positiveTwistTransition 𝒜 hf hg 5) =
      positiveTwistTransition 𝒜 hf hg 1 := by
  apply LinearEquiv.ext
  intro x
  change (((degreeOneRatioUnit 𝒜 hf hg)⁻¹) ^ 5) •
      ((degreeOneRatioUnit 𝒜 hf hg) ^ 4) • x =
    (((degreeOneRatioUnit 𝒜 hf hg)⁻¹) ^ 1) • x
  rw [← mul_smul]
  congr 1
  simp [pow_succ, mul_assoc]

/-! ## The triple-overlap cocycle -/

/-- The ratio `g/f` represented on the ordered triple overlap
`D₊(fgh)`. -/
def degreeOneRatio12 {f g h : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hh : h ∈ 𝒜 1) :
    HomogeneousLocalization.Away 𝒜 ((f * g) * h) :=
  HomogeneousLocalization.Away.mk 𝒜
    (SetLike.mul_mem_graded (SetLike.mul_mem_graded hf hg) hh) 1
    (g ^ 2 * h) (by
      simpa using SetLike.mul_mem_graded (SetLike.pow_mem_graded 2 hg) hh)

/-- The ratio `h/g` represented on the ordered triple overlap
`D₊(fgh)`. -/
def degreeOneRatio23 {f g h : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hh : h ∈ 𝒜 1) :
    HomogeneousLocalization.Away 𝒜 ((f * g) * h) :=
  HomogeneousLocalization.Away.mk 𝒜
    (SetLike.mul_mem_graded (SetLike.mul_mem_graded hf hg) hh) 1
    (h ^ 2 * f) (by
      simpa using SetLike.mul_mem_graded (SetLike.pow_mem_graded 2 hh) hf)

/-- The ratio `h/f` represented on the ordered triple overlap
`D₊(fgh)`. -/
def degreeOneRatio13 {f g h : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hh : h ∈ 𝒜 1) :
    HomogeneousLocalization.Away 𝒜 ((f * g) * h) :=
  HomogeneousLocalization.Away.mk 𝒜
    (SetLike.mul_mem_graded (SetLike.mul_mem_graded hf hg) hh) 1
    (h ^ 2 * g) (by
      simpa using SetLike.mul_mem_graded (SetLike.pow_mem_graded 2 hh) hg)

/-- Degree-one chart ratios satisfy the multiplicative cocycle identity on a
triple overlap: `(g/f) * (h/g) = h/f`. -/
theorem degreeOneRatio_cocycle {f g h : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hh : h ∈ 𝒜 1) :
    degreeOneRatio12 𝒜 hf hg hh * degreeOneRatio23 𝒜 hf hg hh =
      degreeOneRatio13 𝒜 hf hg hh := by
  ext
  simp only [degreeOneRatio12, degreeOneRatio23, degreeOneRatio13,
    HomogeneousLocalization.val_mul, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp
  ring

/-! ## Restriction from pair overlaps to a common triple overlap -/

/-- Restrict the `fg` overlap ring to the ordered triple overlap `fgh`. -/
def restrict12 {f g h : A} (hh : h ∈ 𝒜 1) :
    HomogeneousLocalization.Away 𝒜 (f * g) →+*
      HomogeneousLocalization.Away 𝒜 ((f * g) * h) :=
  HomogeneousLocalization.awayMap 𝒜 hh rfl

/-- Restrict the `gh` overlap ring to the same ordered triple overlap. -/
def restrict23 {f g h : A} (hf : f ∈ 𝒜 1) :
    HomogeneousLocalization.Away 𝒜 (g * h) →+*
      HomogeneousLocalization.Away 𝒜 ((f * g) * h) :=
  HomogeneousLocalization.awayMap 𝒜 hf (by ring)

/-- Restrict the `fh` overlap ring to the same ordered triple overlap. -/
def restrict13 {f g h : A} (hg : g ∈ 𝒜 1) :
    HomogeneousLocalization.Away 𝒜 (f * h) →+*
      HomogeneousLocalization.Away 𝒜 ((f * g) * h) :=
  HomogeneousLocalization.awayMap 𝒜 hg (by ring)

/-- Restricting `g/f` from the first pair overlap gives its explicit
representative on the triple overlap. -/
theorem restrict12_degreeOneRatio {f g h : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hh : h ∈ 𝒜 1) :
    restrict12 𝒜 hh (degreeOneRatio 𝒜 hf hg) =
      degreeOneRatio12 𝒜 hf hg hh := by
  rw [restrict12, degreeOneRatio, degreeOneRatio12,
    HomogeneousLocalization.awayMap_mk]
  simp only [pow_one]

/-- Restricting `h/g` from the second pair overlap gives its explicit
representative on the triple overlap. -/
theorem restrict23_degreeOneRatio {f g h : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hh : h ∈ 𝒜 1) :
    restrict23 𝒜 hf (degreeOneRatio 𝒜 hg hh) =
      degreeOneRatio23 𝒜 hf hg hh := by
  rw [restrict23, degreeOneRatio, degreeOneRatio23,
    HomogeneousLocalization.awayMap_mk]
  simp only [pow_one]

/-- Restricting `h/f` from the third pair overlap gives its explicit
representative on the triple overlap. -/
theorem restrict13_degreeOneRatio {f g h : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hh : h ∈ 𝒜 1) :
    restrict13 𝒜 hg (degreeOneRatio 𝒜 hf hh) =
      degreeOneRatio13 𝒜 hf hg hh := by
  rw [restrict13, degreeOneRatio, degreeOneRatio13,
    HomogeneousLocalization.awayMap_mk]
  simp only [pow_one]

/-- The pairwise transition ratios satisfy the Čech cocycle after all three
are restricted to a common triple overlap. -/
theorem degreeOneRatio_restricted_cocycle {f g h : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hh : h ∈ 𝒜 1) :
    restrict12 𝒜 hh (degreeOneRatio 𝒜 hf hg) *
        restrict23 𝒜 hf (degreeOneRatio 𝒜 hg hh) =
      restrict13 𝒜 hg (degreeOneRatio 𝒜 hf hh) := by
  rw [restrict12_degreeOneRatio, restrict23_degreeOneRatio,
    restrict13_degreeOneRatio]
  exact degreeOneRatio_cocycle 𝒜 hf hg hh

/-- The transition units themselves satisfy the restricted Čech cocycle. -/
theorem degreeOneRatioUnit_restricted_cocycle {f g h : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hh : h ∈ 𝒜 1) :
    Units.map (restrict12 𝒜 (f := f) (g := g) (h := h) hh).toMonoidHom
        (degreeOneRatioUnit 𝒜 hf hg) *
      Units.map (restrict23 𝒜 (f := f) (g := g) (h := h) hf).toMonoidHom
        (degreeOneRatioUnit 𝒜 hg hh) =
    Units.map (restrict13 𝒜 (f := f) (g := g) (h := h) hg).toMonoidHom
      (degreeOneRatioUnit 𝒜 hf hh) := by
  apply Units.ext
  exact degreeOneRatio_restricted_cocycle 𝒜 hf hg hh

/-- Every integral power of the transition unit satisfies the same restricted
cocycle.  Thus one theorem supplies descent data for all positive and
negative integral twists. -/
theorem degreeOneRatioUnit_zpow_restricted_cocycle {f g h : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hh : h ∈ 𝒜 1) (d : ℤ) :
    (Units.map (restrict12 𝒜 (f := f) (g := g) (h := h) hh).toMonoidHom
        (degreeOneRatioUnit 𝒜 hf hg)) ^ d *
      (Units.map (restrict23 𝒜 (f := f) (g := g) (h := h) hf).toMonoidHom
        (degreeOneRatioUnit 𝒜 hg hh)) ^ d =
    (Units.map (restrict13 𝒜 (f := f) (g := g) (h := h) hg).toMonoidHom
      (degreeOneRatioUnit 𝒜 hf hh)) ^ d := by
  rw [← mul_zpow, degreeOneRatioUnit_restricted_cocycle]

/-! ## Rank-one module descent isomorphisms -/

/-- An integral power of the chart ratio gives a linear transition on a pair
overlap.  Exponent `d` corresponds to the transition of `O(-d)`. -/
def ratioPowerTransition {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)
    (d : ℤ) :
    HomogeneousLocalization.Away 𝒜 (f * g) ≃ₗ[HomogeneousLocalization.Away 𝒜 (f * g)]
      HomogeneousLocalization.Away 𝒜 (f * g) :=
  DistribMulAction.toLinearEquiv (HomogeneousLocalization.Away 𝒜 (f * g))
    (HomogeneousLocalization.Away 𝒜 (f * g)) ((degreeOneRatioUnit 𝒜 hf hg) ^ d)

/-- The first pair transition after restriction to the ordered triple
overlap. -/
def ratioPowerTransition12 {f g h : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hh : h ∈ 𝒜 1) (d : ℤ) :
    HomogeneousLocalization.Away 𝒜 ((f * g) * h) ≃ₗ[
      HomogeneousLocalization.Away 𝒜 ((f * g) * h)]
      HomogeneousLocalization.Away 𝒜 ((f * g) * h) :=
  DistribMulAction.toLinearEquiv _ _
    ((Units.map (restrict12 𝒜 (f := f) (g := g) (h := h) hh).toMonoidHom
      (degreeOneRatioUnit 𝒜 hf hg)) ^ d)

/-- The second pair transition after restriction to the ordered triple
overlap. -/
def ratioPowerTransition23 {f g h : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hh : h ∈ 𝒜 1) (d : ℤ) :
    HomogeneousLocalization.Away 𝒜 ((f * g) * h) ≃ₗ[
      HomogeneousLocalization.Away 𝒜 ((f * g) * h)]
      HomogeneousLocalization.Away 𝒜 ((f * g) * h) :=
  DistribMulAction.toLinearEquiv _ _
    ((Units.map (restrict23 𝒜 (f := f) (g := g) (h := h) hf).toMonoidHom
      (degreeOneRatioUnit 𝒜 hg hh)) ^ d)

/-- The direct first-to-third transition after restriction to the ordered
triple overlap. -/
def ratioPowerTransition13 {f g h : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hh : h ∈ 𝒜 1) (d : ℤ) :
    HomogeneousLocalization.Away 𝒜 ((f * g) * h) ≃ₗ[
      HomogeneousLocalization.Away 𝒜 ((f * g) * h)]
      HomogeneousLocalization.Away 𝒜 ((f * g) * h) :=
  DistribMulAction.toLinearEquiv _ _
    ((Units.map (restrict13 𝒜 (f := f) (g := g) (h := h) hg).toMonoidHom
      (degreeOneRatioUnit 𝒜 hf hh)) ^ d)

/-- The restricted linear transition equivalences satisfy the descent
cocycle: the first-to-second map followed by the second-to-third map is the
first-to-third map. -/
theorem ratioPowerTransition_cocycle {f g h : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hh : h ∈ 𝒜 1) (d : ℤ) :
    (ratioPowerTransition12 𝒜 hf hg hh d).trans
        (ratioPowerTransition23 𝒜 hf hg hh d) =
      ratioPowerTransition13 𝒜 hf hg hh d := by
  apply LinearEquiv.ext
  intro x
  change (Units.map (restrict23 𝒜 (f := f) (g := g) (h := h) hf).toMonoidHom
      (degreeOneRatioUnit 𝒜 hg hh)) ^ d •
    (Units.map (restrict12 𝒜 (f := f) (g := g) (h := h) hh).toMonoidHom
      (degreeOneRatioUnit 𝒜 hf hg)) ^ d • x =
    (Units.map (restrict13 𝒜 (f := f) (g := g) (h := h) hg).toMonoidHom
      (degreeOneRatioUnit 𝒜 hf hh)) ^ d • x
  rw [← mul_smul]
  apply congrArg (fun u : (HomogeneousLocalization.Away 𝒜 ((f * g) * h))ˣ ↦ u • x)
  calc
    (Units.map (restrict23 𝒜 (f := f) (g := g) (h := h) hf).toMonoidHom
          (degreeOneRatioUnit 𝒜 hg hh)) ^ d *
        (Units.map (restrict12 𝒜 (f := f) (g := g) (h := h) hh).toMonoidHom
          (degreeOneRatioUnit 𝒜 hf hg)) ^ d =
      (Units.map (restrict12 𝒜 (f := f) (g := g) (h := h) hh).toMonoidHom
          (degreeOneRatioUnit 𝒜 hf hg)) ^ d *
        (Units.map (restrict23 𝒜 (f := f) (g := g) (h := h) hf).toMonoidHom
          (degreeOneRatioUnit 𝒜 hg hh)) ^ d := mul_comm _ _
    _ = _ := degreeOneRatioUnit_zpow_restricted_cocycle 𝒜 hf hg hh d

/-- The first restricted transition as an isomorphism of free rank-one
modules over the triple-overlap ring. -/
def ratioPowerModuleIso12 {f g h : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hh : h ∈ 𝒜 1) (d : ℤ) :=
  (ratioPowerTransition12 𝒜 hf hg hh d).toModuleIso

/-- The second restricted transition as an isomorphism of free rank-one
modules over the triple-overlap ring. -/
def ratioPowerModuleIso23 {f g h : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hh : h ∈ 𝒜 1) (d : ℤ) :=
  (ratioPowerTransition23 𝒜 hf hg hh d).toModuleIso

/-- The direct restricted transition as an isomorphism of free rank-one
modules over the triple-overlap ring. -/
def ratioPowerModuleIso13 {f g h : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hh : h ∈ 𝒜 1) (d : ℤ) :=
  (ratioPowerTransition13 𝒜 hf hg hh d).toModuleIso

/-- The rank-one module isomorphisms satisfy the categorical descent
cocycle on every ordered triple overlap. -/
theorem ratioPowerModuleIso_cocycle {f g h : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1) (hh : h ∈ 𝒜 1) (d : ℤ) :
    (ratioPowerModuleIso12 𝒜 hf hg hh d).hom ≫
        (ratioPowerModuleIso23 𝒜 hf hg hh d).hom =
      (ratioPowerModuleIso13 𝒜 hf hg hh d).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact LinearEquiv.congr_fun (ratioPowerTransition_cocycle 𝒜 hf hg hh d) x

end HomogeneousLocalization.Away
