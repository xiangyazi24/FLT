import FLT.Assumptions.MazurProof.N18MumfordGroup
import FLT.Assumptions.MazurProof.N18RouteC_Curve

/-!
# Explicit Abel--Jacobi representatives for the N18 curve

With `∞₊` as base point, an affine point `(x,y)` is represented by the
balanced triple `(X-x, y, 0)`.  The other infinity is `(1,0,0)`, while `∞₊`
is the balanced zero `(1,0,1)`.
-/

open Polynomial

namespace MazurProof.N18Mumford

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

theorem f_eval_eq_curvePolynomial (x : K) :
    (f K).eval x = N18RouteC.curvePolynomial x := by
  simp [f, N18RouteC.curvePolynomial]

def affinePointMumford (x y : K)
    (h : y ^ 2 = N18RouteC.curvePolynomial x) : Mumford K where
  u := X - C x
  v := C y
  nInf := 0
  u_monic := monic_X_sub_C x
  deg_u := by simp
  v_reduced := by
    rw [mod_eq_self_iff (monic_X_sub_C x).ne_zero]
    exact degree_C_le.trans_lt (by rw [degree_X_sub_C]; norm_num)
  curve_dvd := by
    have heval : (f K - (C y) ^ 2).eval x = 0 := by
      rw [eval_sub, eval_pow, eval_C, f_eval_eq_curvePolynomial, ← h,
        sub_self]
    have hd := X_sub_C_dvd_sub_C_eval (p := f K - (C y) ^ 2) (a := x)
    simpa only [heval, C_0, sub_zero] using hd
  infinity_bound := by simp

def infinityMinusMumford : Mumford K where
  u := 1
  v := 0
  nInf := 0
  u_monic := monic_one
  deg_u := by simp
  v_reduced := by simp
  curve_dvd := one_dvd _
  infinity_bound := by simp

def pointMumford : N18RouteC.CurvePoint K → Mumford K
  | .infinityPlus => zero K
  | .infinityMinus => infinityMinusMumford K
  | .affine x y h => affinePointMumford K x y h

theorem X_sub_C_ne_one (x : K) : (X - C x : K[X]) ≠ 1 := by
  intro h
  have hc := congrArg (fun p : K[X] => p.coeff 1) h
  rw [coeff_one] at hc
  have : (1 : K) = 0 := by simpa using hc
  exact one_ne_zero this

theorem X_sub_C_injective :
    Function.Injective (fun x : K => (X - C x : K[X])) := by
  intro x y h
  have hc := congrArg (fun p : K[X] => p.coeff 0) h
  simpa using congrArg Neg.neg hc

theorem pointMumford_injective : Function.Injective (pointMumford K) := by
  intro P Q hPQ
  cases P with
  | infinityPlus =>
      cases Q with
      | infinityPlus => rfl
      | infinityMinus =>
          have hn := congrArg Mumford.nInf hPQ
          norm_num [pointMumford, zero, infinityMinusMumford] at hn
      | affine x y h =>
          have hn := congrArg Mumford.nInf hPQ
          norm_num [pointMumford, zero, affinePointMumford] at hn
  | infinityMinus =>
      cases Q with
      | infinityPlus =>
          have hn := congrArg Mumford.nInf hPQ
          norm_num [pointMumford, zero, infinityMinusMumford] at hn
      | infinityMinus => rfl
      | affine x y h =>
          have hu := congrArg Mumford.u hPQ
          change (1 : K[X]) = X - C x at hu
          exact False.elim (X_sub_C_ne_one K x hu.symm)
  | affine x y h =>
      cases Q with
      | infinityPlus =>
          have hn := congrArg Mumford.nInf hPQ
          norm_num [pointMumford, zero, affinePointMumford] at hn
      | infinityMinus =>
          have hu := congrArg Mumford.u hPQ
          change X - C x = (1 : K[X]) at hu
          exact False.elim (X_sub_C_ne_one K x hu)
      | affine x' y' h' =>
          have hu := congrArg Mumford.u hPQ
          have hv := congrArg Mumford.v hPQ
          change X - C x = X - C x' at hu
          change C y = C y' at hv
          have hx : x = x' := X_sub_C_injective K hu
          have hy : y = y' := C_injective hv
          subst x'
          subst y'
          rfl

def abelJacobi [NormalFormData K] :
    N18RouteC.CurvePoint K → ConcretePic K :=
  fun P => classOf K (pointMumford K P)

theorem abelJacobi_injective [NormalFormData K] :
    Function.Injective (abelJacobi K) := by
  intro P Q hPQ
  apply pointMumford_injective K
  exact classOf_injective K hPQ

end

end MazurProof.N18Mumford
