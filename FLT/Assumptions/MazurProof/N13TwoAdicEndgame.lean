import FLT.Assumptions.MazurProof.N13SymmetricSquareTwo
import FLT.Assumptions.MazurProof.N18RouteC_Separated

/-!
# The N13 two-adic endgame without Mordell--Weil finite generation

A trivial fake two-descent says that multiplication by two on `J(ℚ)` is
surjective.  Combining this with a separated two-adic reduction kernel and
the exponent-nineteen special fibre forces all of `J(ℚ)` to have exponent
nineteen.  If multiplication by nineteen is injective on the formal kernel
(because nineteen is a two-adic unit), reduction is injective.

This file formalizes that group-theoretic chain.  It does not replace the
remaining arithmetic tasks by axioms: fake-descent soundness, the reduction
map, and the formal filtration remain explicit hypotheses.
-/

namespace MazurProof.N13TwoAdicEndgame

noncomputable section

open N18RouteC.Separated

/-- Minimal two-adic formal-kernel package.  Doubling raises a separated
filtration, while multiplication by an odd integer preserves the valuation
of the formal parameter. -/
structure FormalKernelData (K : Type*) [AddCommGroup K] where
  filtration : StrictNSmulFiltration K 2
  val : K → ℕ∞
  val_eq_top : ∀ z : K, val z = ⊤ ↔ z = 0
  val_odd_smul :
    ∀ m : ℤ, ¬(2 ∣ m) → ∀ z : K, val (m • z) = val z

namespace FormalKernelData

variable {K : Type*} [AddCommGroup K]

theorem val_zero (D : FormalKernelData K) : D.val 0 = ⊤ :=
  (D.val_eq_top 0).mpr rfl

/-- Odd multiplication has no nonzero kernel in the two-adic formal
kernel. -/
theorem no_odd_torsion
    (D : FormalKernelData K)
    (m : ℤ) (hm : ¬(2 ∣ m))
    (z : K) (hz : m • z = 0) :
    z = 0 := by
  by_contra hne
  have hval :=
    N13TwoAdicEndgame.FormalKernelData.val_odd_smul D m hm z
  rw [hz, D.val_zero] at hval
  exact hne ((D.val_eq_top z).mp hval.symm)

/-- In particular, multiplication by nineteen is injective. -/
theorem nineteen_injective (D : FormalKernelData K) :
    Function.Injective (fun z : K => 19 • z) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply FormalKernelData.no_odd_torsion D 19 (by norm_num)
  have hnat : 19 • (x - y) = 0 := by
    rw [nsmul_sub]
    exact sub_eq_zero.mpr hxy
  calc
    (19 : ℤ) • (x - y) = (19 : ℕ) • (x - y) :=
      natCast_zsmul (x - y) 19
    _ = 0 := hnat

end FormalKernelData

/-- The exact group-theoretic output of a trivial fake two-descent. -/
def TwoSurjective (G : Type*) [AddCommGroup G] : Prop :=
  ∀ P : G, ∃ Q : G, P = 2 • Q

/-- Surjectivity of multiplication by two is weak descent with zero error. -/
theorem weakDescentWitness_of_twoSurjective
    {G : Type*} [AddCommGroup G]
    (htwo : TwoSurjective G) :
    WeakDescentWitness G 2 1 := by
  intro P
  obtain ⟨Q, hQ⟩ := htwo P
  exact ⟨0, Q, by simp, by simpa using hQ⟩

/-- The structural N13 exponent argument. -/
theorem exponent_nineteen
    {G J₂ : Type*}
    [AddCommGroup G] [AddCommGroup J₂] [Finite J₂]
    (abelFibres : N13SymmetricSquareTwo.AbelFiberData J₂)
    (red : G →+ J₂)
    (twoSurjective : TwoSurjective G)
    (separated : NSeparated red.ker 2) :
    ∀ P : G, 19 • P = 0 := by
  have weak : WeakDescentWitness G 2 1 :=
    weakDescentWitness_of_twoSurjective twoSurjective
  have killRed : ∀ Q : J₂, 19 • Q = 0 :=
    N13SymmetricSquareTwo.jacobian_exponent_nineteen abelFibres
  have h := annihilated_of_weakDescent_and_separated
    (AddMonoidHom.id G) Function.injective_id red
    2 1 19 weak killRed separated
  intro P
  simpa [show Nat.lcm 1 19 = 19 by decide] using h P

/-- Once the rational group has exponent nineteen, injectivity of `[19]` on
the formal kernel makes reduction injective. -/
theorem reduction_injective_of_exponent_nineteen
    {G J₂ : Type*}
    [AddCommGroup G] [AddCommGroup J₂]
    (red : G →+ J₂)
    (hexponent : ∀ P : G, 19 • P = 0)
    (formalKernel_nineteen_injective :
      Function.Injective (fun z : red.ker => 19 • z)) :
    Function.Injective red := by
  intro P Q hPQ
  let z : red.ker :=
    ⟨P - Q, by
      change red (P - Q) = 0
      rw [map_sub, hPQ, sub_self]⟩
  have hz19 : 19 • z = 0 := by
    apply Subtype.ext
    change 19 • (P - Q) = 0
    exact hexponent (P - Q)
  have hz0 : z = 0 := by
    apply formalKernel_nineteen_injective
    simpa using hz19
  have hpq0 : P - Q = 0 := by
    simpa [z] using congrArg Subtype.val hz0
  exact sub_eq_zero.mp hpq0

/-- All fixed-instance inputs for the two-adic endgame. -/
structure Data (G J₂ : Type*)
    [AddCommGroup G] [AddCommGroup J₂] [Finite J₂] where
  abelFibres : N13SymmetricSquareTwo.AbelFiberData J₂
  red : G →+ J₂
  twoSurjective : TwoSurjective G
  formalKernel : FormalKernelData red.ker

theorem Data.exponent_nineteen
    {G J₂ : Type*}
    [AddCommGroup G] [AddCommGroup J₂] [Finite J₂]
    (D : Data G J₂) :
    ∀ P : G, 19 • P = 0 :=
  N13TwoAdicEndgame.exponent_nineteen
    D.abelFibres D.red D.twoSurjective D.formalKernel.filtration.separated

theorem Data.reduction_injective
    {G J₂ : Type*}
    [AddCommGroup G] [AddCommGroup J₂] [Finite J₂]
    (D : Data G J₂) :
    Function.Injective D.red :=
  reduction_injective_of_exponent_nineteen D.red
    D.exponent_nineteen
      (FormalKernelData.nineteen_injective D.formalKernel)

end

end MazurProof.N13TwoAdicEndgame
