import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.FractionalIdeal.Inverse

/-!
# Two-chart lifting of finite trace relations

This file isolates the structural Čech argument needed by the integral
N13 proof.  A special kernel element is lifted chartwise and its overlap
mismatch is corrected before evaluation.  Applying the construction to a
module and its inverse-transition module preserves every product inside
the corresponding multiplier defect ideal.

No projectivity, choice of a generator, or scalar correction after
evaluation is used.
-/

open scoped BigOperators

namespace MazurProof.N13CechTraceLift

variable {R : Type*} [CommRing R]

/-- The two-chart restriction difference with a transition on the second
chart. -/
def twistedCoboundary
    {U V T : Type*}
    [AddCommGroup U] [Module R U]
    [AddCommGroup V] [Module R V]
    [AddCommGroup T] [Module R T]
    (resU : U →ₗ[R] T)
    (resV : V →ₗ[R] T)
    (transition : T →ₗ[R] T) :
    U × V →ₗ[R] T where
  toFun p := resU p.1 - transition (resV p.2)
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel
  map_smul' a p := by simp [smul_sub]

/-- Pairings of sections with mutually inverse transitions glue to an
untwisted scalar. -/
theorem pairing_glues
    {MU MV MT NU NV NT P : Type*}
    [AddCommGroup MU] [Module R MU]
    [AddCommGroup MV] [Module R MV]
    [AddCommGroup MT] [Module R MT]
    [AddCommGroup NU] [Module R NU]
    [AddCommGroup NV] [Module R NV]
    [AddCommGroup NT] [Module R NT]
    (resMU : MU →ₗ[R] MT)
    (resMV : MV →ₗ[R] MT)
    (resNU : NU →ₗ[R] NT)
    (resNV : NV →ₗ[R] NT)
    (transitionM : MT →ₗ[R] MT)
    (transitionN : NT →ₗ[R] NT)
    (pairOverlap : MT → NT → P)
    (htransition :
      ∀ m n,
        pairOverlap (transitionM m) (transitionN n) =
          pairOverlap m n)
    (s :
      LinearMap.ker
        (twistedCoboundary resMU resMV transitionM))
    (t :
      LinearMap.ker
        (twistedCoboundary resNU resNV transitionN)) :
    pairOverlap (resMU s.1.1) (resNU t.1.1) =
      pairOverlap (resMV s.1.2) (resNV t.1.2) := by
  have hs :
      resMU s.1.1 = transitionM (resMV s.1.2) := by
    apply sub_eq_zero.mp
    have hsKernel :
        twistedCoboundary resMU resMV transitionM s.1 = 0 :=
      LinearMap.mem_ker.mp s.2
    exact hsKernel
  have ht :
      resNU t.1.1 = transitionN (resNV t.1.2) := by
    apply sub_eq_zero.mp
    have htKernel :
        twistedCoboundary resNU resNV transitionN t.1 = 0 :=
      LinearMap.mem_ker.mp t.2
    exact htKernel
  calc
    pairOverlap (resMU s.1.1) (resNU t.1.1) =
        pairOverlap
          (transitionM (resMV s.1.2))
          (transitionN (resNV t.1.2)) := by
      rw [hs, ht]
    _ = pairOverlap (resMV s.1.2) (resNV t.1.2) :=
      htransition _ _

/-- Correct a raw lift of a special kernel element by one divisible
coboundary.  Surjectivity of the integral coboundary removes the divided
overlap mismatch without changing reduction. -/
theorem exists_kernel_lift_of_surjective_coboundary
    {X Y X₀ Y₀ : Type*}
    [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y]
    [AddCommGroup X₀] [AddCommGroup Y₀]
    (uniformizer : R)
    (coboundary : X →ₗ[R] Y)
    (specialCoboundary : X₀ →+ Y₀)
    (reduceSource : X →+ X₀)
    (reduceOverlap : Y →+ Y₀)
    (reduce_coboundary :
      ∀ x,
        reduceOverlap (coboundary x) =
          specialCoboundary (reduceSource x))
    (reduceSource_surjective :
      Function.Surjective reduceSource)
    (reduceSource_uniformizer :
      ∀ x, reduceSource (uniformizer • x) = 0)
    (overlap_kernel_divisible :
      ∀ y,
        reduceOverlap y = 0 →
          ∃ e, y = uniformizer • e)
    (coboundary_surjective :
      Function.Surjective coboundary)
    (x₀ : AddMonoidHom.ker specialCoboundary) :
    ∃ x : LinearMap.ker coboundary,
      reduceSource x.1 = x₀.1 := by
  obtain ⟨x, hx⟩ :=
    reduceSource_surjective x₀.1
  have hzero :
      reduceOverlap (coboundary x) = 0 := by
    calc
      reduceOverlap (coboundary x) =
          specialCoboundary (reduceSource x) :=
        reduce_coboundary x
      _ = specialCoboundary x₀.1 := by rw [hx]
      _ = 0 := x₀.2
  obtain ⟨e, he⟩ :=
    overlap_kernel_divisible (coboundary x) hzero
  obtain ⟨correction, hcorrection⟩ :=
    coboundary_surjective e
  refine
    ⟨⟨x - uniformizer • correction, ?_⟩, ?_⟩
  · simp [he, hcorrection]
  · simp [hx, reduceSource_uniformizer]

/-- Variant requiring only one explicit raw chartwise lift.  This avoids a
false global reduction-surjectivity claim for constrained complete-chart
modules. -/
theorem exists_kernel_lift_of_raw_lift
    {X Y X₀ Y₀ : Type*}
    [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y]
    [AddCommGroup X₀] [AddCommGroup Y₀]
    (uniformizer : R)
    (coboundary : X →ₗ[R] Y)
    (specialCoboundary : X₀ →+ Y₀)
    (reduceSource : X →+ X₀)
    (reduceOverlap : Y →+ Y₀)
    (reduce_coboundary :
      ∀ x,
        reduceOverlap (coboundary x) =
          specialCoboundary (reduceSource x))
    (reduceSource_uniformizer :
      ∀ x, reduceSource (uniformizer • x) = 0)
    (overlap_kernel_divisible :
      ∀ y,
        reduceOverlap y = 0 →
          ∃ e, y = uniformizer • e)
    (coboundary_surjective :
      Function.Surjective coboundary)
    (x₀ : AddMonoidHom.ker specialCoboundary)
    (rawLift : X)
    (reduce_rawLift :
      reduceSource rawLift = x₀.1) :
    ∃ x : LinearMap.ker coboundary,
      reduceSource x.1 = x₀.1 := by
  have hzero :
      reduceOverlap (coboundary rawLift) = 0 := by
    calc
      reduceOverlap (coboundary rawLift) =
          specialCoboundary (reduceSource rawLift) :=
        reduce_coboundary rawLift
      _ = specialCoboundary x₀.1 := by
        rw [reduce_rawLift]
      _ = 0 := x₀.2
  obtain ⟨e, he⟩ :=
    overlap_kernel_divisible
      (coboundary rawLift) hzero
  obtain ⟨correction, hcorrection⟩ :=
    coboundary_surjective e
  refine
    ⟨⟨rawLift - uniformizer • correction, ?_⟩, ?_⟩
  · simp [he, hcorrection]
  · simp [reduce_rawLift, reduceSource_uniformizer]

/-- Lift a finite special pairing relation after compatible kernel lifts
have been constructed for both mutually twisted factors. -/
theorem lift_finite_pairing_relation
    {XM YM XN YN XM₀ YM₀ XN₀ YN₀ Q k : Type*}
    [AddCommGroup XM] [Module R XM]
    [AddCommGroup YM] [Module R YM]
    [AddCommGroup XN] [Module R XN]
    [AddCommGroup YN] [Module R YN]
    [AddCommGroup XM₀] [AddCommGroup YM₀]
    [AddCommGroup XN₀] [AddCommGroup YN₀]
    [AddCommGroup Q] [CommRing k]
    (coboundaryM : XM →ₗ[R] YM)
    (specialCoboundaryM : XM₀ →+ YM₀)
    (coboundaryN : XN →ₗ[R] YN)
    (specialCoboundaryN : XN₀ →+ YN₀)
    (reduceM : XM →+ XM₀)
    (reduceN : XN →+ XN₀)
    (liftM :
      ∀ x₀ : AddMonoidHom.ker specialCoboundaryM,
        ∃ x : LinearMap.ker coboundaryM,
          reduceM x.1 = x₀.1)
    (liftN :
      ∀ x₀ : AddMonoidHom.ker specialCoboundaryN,
        ∃ x : LinearMap.ker coboundaryN,
          reduceN x.1 = x₀.1)
    (pair : XM → XN → Q)
    (specialPair : XM₀ → XN₀ → k)
    (reducePair : Q →+ k)
    (reduce_pair :
      ∀ x y,
        reducePair (pair x y) =
          specialPair (reduceM x) (reduceN y))
    {n : ℕ}
    (s₀ : Fin n → AddMonoidHom.ker specialCoboundaryM)
    (t₀ : Fin n → AddMonoidHom.ker specialCoboundaryN)
    (special_relation :
      (∑ i, specialPair (s₀ i).1 (t₀ i).1) = 1) :
    ∃ s : Fin n → LinearMap.ker coboundaryM,
    ∃ t : Fin n → LinearMap.ker coboundaryN,
      (∀ i, reduceM (s i).1 = (s₀ i).1) ∧
      (∀ i, reduceN (t i).1 = (t₀ i).1) ∧
      reducePair (∑ i, pair (s i).1 (t i).1) = 1 := by
  classical
  let s : Fin n → LinearMap.ker coboundaryM :=
    fun i => Classical.choose (liftM (s₀ i))
  have hs :
      ∀ i, reduceM (s i).1 = (s₀ i).1 := by
    intro i
    simpa [s] using
      Classical.choose_spec (liftM (s₀ i))
  let t : Fin n → LinearMap.ker coboundaryN :=
    fun i => Classical.choose (liftN (t₀ i))
  have ht :
      ∀ i, reduceN (t i).1 = (t₀ i).1 := by
    intro i
    simpa [t] using
      Classical.choose_spec (liftN (t₀ i))
  refine ⟨s, t, hs, ht, ?_⟩
  calc
    reducePair (∑ i, pair (s i).1 (t i).1) =
        ∑ i, reducePair (pair (s i).1 (t i).1) := by
      simp
    _ =
        ∑ i,
          specialPair
            (reduceM (s i).1) (reduceN (t i).1) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact reduce_pair _ _
    _ =
        ∑ i, specialPair (s₀ i).1 (t₀ i).1 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hs i, ht i]
    _ = 1 := special_relation

end MazurProof.N13CechTraceLift
