import Mathlib.RingTheory.AdjoinRoot

/-!
# Elements of a linear polynomial quotient are scalar

A quotient by a monic polynomial of degree one has rank one over the
ground field.  Reducing an arbitrary representative modulo that polynomial
therefore gives a constant.  This is the degree-one degeneration of the
quadratic quotient step used in the N13 inverse Kummer construction.
-/

namespace MazurProof.LinearAdjoinRootScalar

noncomputable section

open Polynomial

variable {K : Type*} [Field K]

/-- Every element of a quotient by a monic linear polynomial comes from the
ground field. -/
theorem exists_eq_algebraMap
    (u : K[X]) (hu : u.Monic) (hu1 : u.natDegree = 1)
    (t : AdjoinRoot u) :
    ∃ r : K, t = algebraMap K (AdjoinRoot u) r := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective t
  let rpoly : K[X] := p %ₘ u
  have huNeOne : u ≠ 1 := by
    intro h
    rw [h, natDegree_one] at hu1
    omega
  have hrpoly : rpoly.natDegree ≤ 0 := by
    have hlt := natDegree_modByMonic_lt p hu huNeOne
    dsimp only [rpoly]
    rw [hu1] at hlt
    omega
  refine ⟨rpoly.coeff 0, ?_⟩
  have hrpolyEq : rpoly = C (rpoly.coeff 0) :=
    eq_C_of_natDegree_le_zero hrpoly
  calc
    AdjoinRoot.mk u p =
        AdjoinRoot.mk u
          (AdjoinRoot.modByMonicHom hu (AdjoinRoot.mk u p)) := by
            exact (AdjoinRoot.mk_leftInverse hu
              (AdjoinRoot.mk u p)).symm
    _ = AdjoinRoot.mk u rpoly := by
      rw [AdjoinRoot.modByMonicHom_mk]
    _ = AdjoinRoot.mk u (C (rpoly.coeff 0)) := by
      exact congrArg (AdjoinRoot.mk u) hrpolyEq
    _ = algebraMap K (AdjoinRoot u) (rpoly.coeff 0) := by
      rfl

/-- If an element of a monic linear quotient has scalar square `s`, then its
unique scalar representative is a square root of `s`. -/
theorem exists_scalar_square_root
    (u : K[X]) (hu : u.Monic) (hu1 : u.natDegree = 1)
    (t : AdjoinRoot u) (s : K)
    (hsq : t ^ 2 = algebraMap K (AdjoinRoot u) s) :
    ∃ r : K,
      t = algebraMap K (AdjoinRoot u) r ∧ r ^ 2 = s := by
  obtain ⟨r, hr⟩ := exists_eq_algebraMap u hu hu1 t
  refine ⟨r, hr, ?_⟩
  have hscalar :
      algebraMap K (AdjoinRoot u) (r ^ 2) =
        algebraMap K (AdjoinRoot u) s := by
    rw [map_pow, ← hr, hsq]
  have hdegree : u.degree ≠ 0 := by
    rw [degree_eq_natDegree hu.ne_zero, hu1]
    norm_num
  exact
    (AdjoinRoot.of.injective_of_degree_ne_zero hdegree) hscalar

end

end MazurProof.LinearAdjoinRootScalar
