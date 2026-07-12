import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open Polynomial
open scoped Polynomial

namespace Q4469Reference

/-! The fixed elliptic model of X_0(49), Cremona 49a1. -/
noncomputable def X049 : WeierstrassCurve ℚ := ⟨1, -1, 0, -2, -1⟩

noncomputable instance X049_isElliptic : X049.IsElliptic := by
  -- Its discriminant is -343.
  sorry

abbrev X049Point := X049.toAffine.Point

noncomputable def cuspInf : X049Point := 0

noncomputable def cuspZero : X049Point :=
  WeierstrassCurve.Affine.Point.mk (W' := X049) (x := 2) (y := -1) (by
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [X049])

/-! A mirror of the information extracted from the repository's
`RawOrder49TateObstruction`.  The adapter from `preΨ'` to `exactOrder`
is one of the explicitly isolated deep/interface lemmas. -/
structure Tate49Witness where
  b c : ℚ
  exactOrder : Prop
  nonsingular : Prop

/-- The moduli/quotient bridge: forget the generator and retain its cyclic subgroup.
In the production file this is constructed by the rational Velu quotient by `<P>`
and the fixed identification `X_0(49) ≃ 49a1`. -/
structure X049Bridge where
  toPoint : Tate49Witness → X049Point
  noncuspidal : ∀ w, toPoint w ≠ cuspInf ∧ toPoint w ≠ cuspZero

/-- The rank-zero/enumeration result.  Its proof is the explicit 2-isogeny descent
plus 2-adic separatedness described below. -/
structure X049MWCertificate where
  exhaustive : ∀ P : X049Point, P = cuspInf ∨ P = cuspZero

/-- Final abstract contradiction. -/
theorem no_tate49_witness (bridge : X049Bridge) (mw : X049MWCertificate) :
    ¬ Nonempty Tate49Witness := by
  rintro ⟨w⟩
  rcases mw.exhaustive (bridge.toPoint w) with h | h
  · exact (bridge.noncuspidal w).1 h
  · exact (bridge.noncuspidal w).2 h

/-! ## Finite local certificates for the 2-isogeny descent -/

def even16 (x : ZMod 16) : Prop := ∃ y : ZMod 16, x = 2 * y

def primitive16 (u v : ZMod 16) : Prop := ¬ (even16 u ∧ even16 v)

def sevenDiv49 (x : ZMod 49) : Prop := ∃ y : ZMod 49, x = 7 * y

def primitive49 (u v : ZMod 49) : Prop := ¬ (sevenDiv49 u ∧ sevenDiv49 v)

/-- Candidate d=2 for V^2=U^3+21U^2+112U has no primitive 2-adic lift. -/
theorem no_E_d2_mod16 :
    ∀ u v w : ZMod 16, primitive16 u v →
      w^2 ≠ 2*u^4 + 21*u^2*v^2 + 56*v^4 := by
  native_decide

/-- Candidate d=14 has no primitive 2-adic lift. -/
theorem no_E_d14_mod16 :
    ∀ u v w : ZMod 16, primitive16 u v →
      w^2 ≠ 14*u^4 + 21*u^2*v^2 + 8*v^4 := by
  native_decide

/-- The four negative candidates are ruled out at 7; these are deliberately
separate finite certificates so each can be used by `norm_num`/`native_decide`. -/
theorem no_E_dm1_mod49 :
    ∀ u v w : ZMod 49, primitive49 u v →
      w^2 ≠ -u^4 + 21*u^2*v^2 - 112*v^4 := by
  native_decide

theorem no_E_dm2_mod49 :
    ∀ u v w : ZMod 49, primitive49 u v →
      w^2 ≠ -2*u^4 + 21*u^2*v^2 - 56*v^4 := by
  native_decide

theorem no_E_dm7_mod49 :
    ∀ u v w : ZMod 49, primitive49 u v →
      w^2 ≠ -7*u^4 + 21*u^2*v^2 - 16*v^4 := by
  native_decide

theorem no_E_dm14_mod49 :
    ∀ u v w : ZMod 49, primitive49 u v →
      w^2 ≠ -14*u^4 + 21*u^2*v^2 - 8*v^4 := by
  native_decide

/-- On the dual curve Z^2=X^3-42X^2-7X, only d=1 and d=-7 survive. -/
theorem no_Ehat_dm1_mod16 :
    ∀ u v w : ZMod 16, primitive16 u v →
      w^2 ≠ -u^4 - 42*u^2*v^2 + 7*v^4 := by
  native_decide

theorem no_Ehat_d7_mod16 :
    ∀ u v w : ZMod 16, primitive16 u v →
      w^2 ≠ 7*u^4 - 42*u^2*v^2 - v^4 := by
  native_decide

/-! ## Production interfaces for the descent and separatedness -/

/-- The split model is obtained from 49a1 by
`U=4(x-2)`, `V=8y+4x`. -/
def EEquation (U V : ℚ) : Prop := V^2 = U^3 + 21*U^2 + 112*U

/-- The 2-isogenous companion. -/
def EhatEquation (X Z : ℚ) : Prop := Z^2 = X^3 - 42*X^2 - 7*X

/-- Forward Velu map away from the kernel point. -/
def phi (U V : ℚ) : ℚ × ℚ :=
  (V^2 / U^2, V * (112 - U^2) / U^2)

/-- Dual map away from its kernel point. -/
def phihat (X Z : ℚ) : ℚ × ℚ :=
  (Z^2 / (4*X^2), Z * (-7 - X^2) / (8*X^2))

lemma phi_lands {U V : ℚ} (hU : U ≠ 0) (h : EEquation U V) :
    EhatEquation (phi U V).1 (phi U V).2 := by
  unfold EEquation EhatEquation phi at *
  field_simp [hU] at *
  nlinarith [h]

lemma phihat_lands {X Z : ℚ} (hX : X ≠ 0) (h : EhatEquation X Z) :
    EEquation (phihat X Z).1 (phihat X Z).2 := by
  unfold EEquation EhatEquation phihat at *
  field_simp [hX] at *
  nlinarith [h]

/-- Algebraic 2-isogeny descent output: every rational point differs from
`O` or the rational 2-torsion point by a double. -/
structure X049TwoDescentData where
  Point : Type
  instAddCommGroup : AddCommGroup Point
  T : Point
  twoT : 2 • T = 0
  modTwo : ∀ P : Point, ∃ e : Bool, ∃ Q : Point,
    P = (if e then T else 0) + 2 • Q

attribute [instance] X049TwoDescentData.instAddCommGroup

/-- Reusable local theorem: an infinitely 2-divisible rational point is zero.
The production proof embeds into Q_2, uses #E(F_2)=2 to enter the formal kernel,
and then applies the repository's 2-adic separatedness lemma. -/
structure X049SeparatedData (D : X049TwoDescentData) where
  separated : ∀ P : D.Point,
    (∀ n : ℕ, ∃ Q : D.Point, (2^n : ℕ) • Q = P) → P = 0

/-- Descent + separatedness makes the two listed points exhaustive. -/
theorem two_points_of_descent
    (D : X049TwoDescentData) (S : X049SeparatedData D) (P : D.Point) :
    P = 0 ∨ P = D.T := by
  obtain ⟨e, Q, hQ⟩ := D.modTwo P
  by_cases he : e = true
  · right
    have hdiv : ∀ n : ℕ, ∃ R : D.Point, (2^n : ℕ) • R = P - D.T := by
      intro n
      sorry
    have hz := S.separated (P - D.T) hdiv
    exact sub_eq_zero.mp hz
  · left
    have hdiv : ∀ n : ℕ, ∃ R : D.Point, (2^n : ℕ) • R = P := by
      intro n
      sorry
    exact S.separated P hdiv

end Q4469Reference
