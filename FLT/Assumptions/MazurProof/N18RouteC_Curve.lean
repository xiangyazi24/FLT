import FLT.Assumptions.MazurProof.N18RouteC_Split

/-!
# The fixed smooth-projective point presentation for N18

For the Route C integration seams we only need the two rational points at
infinity and the affine sextic chart.  This explicit point type is shared by
the modular bridge and the finite-exhaustion interface.
-/

namespace MazurProof.N18RouteC

noncomputable section

def curvePolynomial {K : Type*} [CommRing K] (x : K) : K :=
  x ^ 6 + 4 * x ^ 5 + 10 * x ^ 4 + 10 * x ^ 3 +
    5 * x ^ 2 + 2 * x + 1

inductive CurvePoint (K : Type*) [CommRing K] where
  | infinityPlus
  | infinityMinus
  | affine (x y : K) (onCurve : y ^ 2 = curvePolynomial x)

namespace CurvePoint

variable {K K' : Type*} [CommRing K] [CommRing K']

def IsCusp : CurvePoint K → Prop
  | .infinityPlus => True
  | .infinityMinus => True
  | .affine x y _ =>
      (x = 0 ∧ (y = 1 ∨ y = -1)) ∨
      (x = -1 ∧ (y = 1 ∨ y = -1))

theorem affine_not_cusp_of_x_ne
    {x y : K} {h : y ^ 2 = curvePolynomial x}
    (hx0 : x ≠ 0) (hx1 : x ≠ -1) :
    ¬ IsCusp (.affine x y h) := by
  intro hc
  change
    (x = 0 ∧ (y = 1 ∨ y = -1)) ∨
      (x = -1 ∧ (y = 1 ∨ y = -1)) at hc
  rcases hc with hc | hc
  · exact hx0 hc.1
  · exact hx1 hc.1

theorem curvePolynomial_map (ι : K →+* K') (x : K) :
    ι (curvePolynomial x) = curvePolynomial (ι x) := by
  simp only [curvePolynomial, map_add, map_mul, map_pow, map_ofNat, map_one]

def map (ι : K →+* K') : CurvePoint K → CurvePoint K'
  | .infinityPlus => .infinityPlus
  | .infinityMinus => .infinityMinus
  | .affine x y h => .affine (ι x) (ι y) <| by
      rw [← curvePolynomial_map ι]
      simpa only [map_pow] using congrArg ι h

theorem map_injective (ι : K →+* K') (hι : Function.Injective ι) :
    Function.Injective (map ι) := by
  intro P Q hPQ
  cases P with
  | infinityPlus => cases Q <;> simp_all [map]
  | infinityMinus => cases Q <;> simp_all [map]
  | affine x y hx =>
      cases Q with
      | infinityPlus => simp [map] at hPQ
      | infinityMinus => simp [map] at hPQ
      | affine x' y' hy =>
          simp only [map, affine.injEq] at hPQ
          obtain ⟨hxm, hym⟩ := hPQ
          have hxeq : x = x' := hι hxm
          have hyeq : y = y' := hι hym
          subst x'
          subst y'
          rfl

end CurvePoint

abbrev CurvePointQ := CurvePoint ℚ
abbrev CurvePointL := CurvePoint L

def baseChangePoint : CurvePointQ → CurvePointL :=
  CurvePoint.map (algebraMap ℚ L)

theorem baseChangePoint_injective : Function.Injective baseChangePoint :=
  CurvePoint.map_injective (algebraMap ℚ L) (algebraMap ℚ L).injective

@[simp]
theorem curvePolynomial_L_eq_curveF (x : L) : curvePolynomial x = curveF x := rfl

end

end MazurProof.N18RouteC
