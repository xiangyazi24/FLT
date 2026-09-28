import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoQuotientGrading
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic

/-!
# Hilbert function of the literal binary canonical-cone pieces

The existing degreewise Koszul sequence has terms

  0 -> shiftedPiece 5 n
    -> shiftedPiece 2 n × shiftedPiece 3 n
    -> shiftedPiece 0 n
    -> canonicalConePiece n -> 0.

The existing canonicalConePieceLinearEquiv identifies the last term with
literalConePiece n.  All dimension arithmetic below is in Nat, not in the
coefficient field ZMod 2.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MazurProof.N25F_GradedConePieceHilbert

open RationalPointsN25QuotientTwoGradedKoszul
open RationalPointsN25QuotientTwoQuotientGrading

/-- A multiset of size t in four variables is its monomial exponent vector.
The degree predicate is definitionally the total-mass predicate used by
Sym.equivNatSum. -/
private def fourVariableExponentEquiv (t : ℕ) :
    Sym (Fin 4) t ≃ {e : Fin 4 →₀ ℕ // e.degree = t} := by
  change Sym (Fin 4) t ≃
    {e : Fin 4 →₀ ℕ // e.sum (fun _ a => a) = t}
  exact Sym.equivNatSum (Fin 4) t

/-- Restrict the ordinary monomial basis to exponent vectors of degree t,
then index it by multisets of size t. -/
private def fourVariableHomogeneousBasis (t : ℕ) :
    Module.Basis (Sym (Fin 4) t) (ZMod 2)
      (MvPolynomial.homogeneousSubmodule (Fin 4) (ZMod 2) t) := by
  classical
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  exact
    (MvPolynomial.basisRestrictSupport (ZMod 2)
      {e : Fin 4 →₀ ℕ | e.degree = t}).reindex
        (fourVariableExponentEquiv t).symm

/-- Only the individual homogeneous pieces, not the whole polynomial ring,
are asserted to be finite-dimensional. -/
local instance homogeneousPieceFinite (t : ℕ) :
    Module.Finite (ZMod 2)
      (MvPolynomial.homogeneousSubmodule (Fin 4) (ZMod 2) t) :=
  Module.Finite.of_basis (fourVariableHomogeneousBasis t)

/-- The four-variable monomial count, obtained from the actual basis and
Mathlib's stars-and-bars theorem. -/
private theorem fourVariableHomogeneous_finrank (t : ℕ) :
    Module.finrank (ZMod 2)
        (MvPolynomial.homogeneousSubmodule (Fin 4) (ZMod 2) t) =
      (t + 3).choose 3 := by
  calc
    Module.finrank (ZMod 2)
        (MvPolynomial.homogeneousSubmodule (Fin 4) (ZMod 2) t) =
        Fintype.card (Sym (Fin 4) t) :=
      Module.finrank_eq_card_basis (fourVariableHomogeneousBasis t)
    _ = (4 + t - 1).choose t := by
      simpa only [Fintype.card_fin] using
        (Sym.card_sym_eq_choose (α := Fin 4) t)
    _ = (t + 3).choose 3 := by
      rw [show 4 + t - 1 = t + 3 by omega]
      exact Nat.choose_symm_add

local instance shiftedPieceFinite (debt n : ℕ) :
    Module.Finite (ZMod 2) (shiftedPiece debt n) := by
  by_cases h : debt ≤ n
  · rw [shiftedPiece, if_pos h]
    infer_instance
  · rw [shiftedPiece, if_neg h]
    infer_instance

/-- The strict below-shift case contributes zero, rather than the degree-zero
homogeneous piece that truncated subtraction alone would produce. -/
private theorem shiftedPiece_finrank_eq (debt n : ℕ) :
    Module.finrank (ZMod 2) (shiftedPiece debt n) =
      if debt ≤ n then (n - debt + 3).choose 3 else 0 := by
  by_cases h : debt ≤ n
  · rw [if_pos h, shiftedPiece, if_pos h]
    exact fourVariableHomogeneous_finrank (n - debt)
  · rw [if_neg h, shiftedPiece, if_neg h]
    exact finrank_bot (ZMod 2) S

/-- The Euler dimension identity for the actual degreewise Koszul sequence,
written additively so that no truncated subtraction is used. -/
private theorem literalConePiece_finrank_balance (n : ℕ) :
    Module.finrank (ZMod 2) (literalConePiece n) +
        Module.finrank (ZMod 2) (shiftedPiece 2 n) +
        Module.finrank (ZMod 2) (shiftedPiece 3 n) =
      Module.finrank (ZMod 2) (shiftedPiece 0 n) +
        Module.finrank (ZMod 2) (shiftedPiece 5 n) := by
  have htopKer : LinearMap.ker (gradedKoszulTop n) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (gradedKoszulTop_injective n)
  have htop := (gradedKoszulTop n).finrank_range_add_finrank_ker
  rw [htopKer, finrank_bot, add_zero] at htop

  have hmiddleKer :
      LinearMap.ker (gradedKoszulMiddle n) =
        LinearMap.range (gradedKoszulTop n) :=
    (LinearMap.exact_iff).mp (gradedKoszul_exact_top_middle n)
  have hmiddle := (gradedKoszulMiddle n).finrank_range_add_finrank_ker
  rw [hmiddleKer, htop, Module.finrank_prod] at hmiddle

  have hquot :
      Module.finrank (ZMod 2) (canonicalConePiece n) +
          Module.finrank (ZMod 2)
            (LinearMap.range (gradedKoszulMiddle n)) =
        Module.finrank (ZMod 2) (shiftedPiece 0 n) :=
    (LinearMap.range (gradedKoszulMiddle n)).finrank_quotient_add_finrank
  rw [(canonicalConePieceLinearEquiv n).finrank_eq] at hquot
  simp only [k] at htop hmiddle hquot ⊢
  omega

/-- A denominator-cleared binomial formula in Nat.  The coefficients here
are not scalars in the binary coefficient field. -/
private theorem six_mul_choose_add_three (t : ℕ) :
    6 * (t + 3).choose 3 = (t + 1) * (t + 2) * (t + 3) := by
  have htwo :
      (t + 2).choose 2 * 2 = (t + 2) * (t + 1) := by
    simpa [Nat.add_assoc] using
      (Nat.add_one_mul_choose_eq (t + 1) 1).symm
  have hthree :
      (t + 3).choose 3 * 3 = (t + 3) * (t + 2).choose 2 := by
    simpa [Nat.add_assoc] using
      (Nat.add_one_mul_choose_eq (t + 2) 2).symm
  calc
    6 * (t + 3).choose 3 = 2 * ((t + 3).choose 3 * 3) := by ring
    _ = 2 * ((t + 3) * (t + 2).choose 2) := by rw [hthree]
    _ = (t + 3) * ((t + 2).choose 2 * 2) := by ring
    _ = (t + 3) * ((t + 2) * (t + 1)) := by rw [htwo]
    _ = (t + 1) * (t + 2) * (t + 3) := by ring

/-- The Hilbert function of the literal canonical-cone grading is 6n - 3
in every degree n at least two. -/
theorem literalConePiece_finrank_eq (n : ℕ) (hn : 2 ≤ n) :
    Module.finrank (ZMod 2)
      (MazurProof.RationalPointsN25QuotientTwoQuotientGrading.literalConePiece n) =
        6 * n - 3 := by
  have hbalance := literalConePiece_finrank_balance n
  by_cases hfive : 5 ≤ n
  · obtain ⟨t, rfl⟩ : ∃ t, n = t + 5 :=
      Nat.exists_eq_add_of_le' hfive
    have hzero : 0 ≤ t + 5 := Nat.zero_le _
    have htwo : 2 ≤ t + 5 := by omega
    have hthree : 3 ≤ t + 5 := by omega
    have hs0 : t + 5 - 0 + 3 = t + 8 := by omega
    have hs2 : t + 5 - 2 + 3 = t + 6 := by omega
    have hs3 : t + 5 - 3 + 3 = t + 5 := by omega
    have hs5 : t + 5 - 5 + 3 = t + 3 := by omega
    simp only [shiftedPiece_finrank_eq, if_pos hzero, if_pos htwo,
      if_pos hthree, if_pos hfive, hs0, hs2, hs3, hs5] at hbalance

    have c0 :
        6 * (t + 8).choose 3 = (t + 6) * (t + 7) * (t + 8) := by
      simpa [Nat.add_assoc] using six_mul_choose_add_three (t + 5)
    have c2 :
        6 * (t + 6).choose 3 = (t + 4) * (t + 5) * (t + 6) := by
      simpa [Nat.add_assoc] using six_mul_choose_add_three (t + 3)
    have c3 :
        6 * (t + 5).choose 3 = (t + 3) * (t + 4) * (t + 5) := by
      simpa [Nat.add_assoc] using six_mul_choose_add_three (t + 2)
    have c5 := six_mul_choose_add_three t
    have hscaled := congrArg (fun a : ℕ => 6 * a) hbalance
    rw [show 6 * (t + 5) - 3 = 6 * t + 27 by omega]
    nlinarith only [hscaled, c0, c2, c3, c5]
  · have hsmall : n < 5 := Nat.lt_of_not_ge hfive
    interval_cases n <;>
      norm_num [shiftedPiece_finrank_eq, Nat.choose] at hbalance ⊢ <;>
      omega

end MazurProof.N25F_GradedConePieceHilbert
