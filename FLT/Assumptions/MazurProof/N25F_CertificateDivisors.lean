import FLT.Assumptions.MazurProof.N25F_RationalPointOrders

/-!
# Four exact divisors and a principal divisor `71·(Z - YZ)`

On the genus-four N25 quotient curve over `F₂`, write `x = qx`, `y = qy`,
`z = qz` for the affine coordinates of the chart `w = 1`, subject to

* `Q : xz + x + y² + yz + z = 0`, and
* `C : x² + xyz + xy + xz + yz + z² + z = 0`.

Writing `lof cX cYZ cZ cR cP` for the divisor supported on the five rational
points `X, YZ, Z, R, P`, we compute

| function      | `X` | `YZ` | `Z` | `R` | `P` |
|---------------|-----|------|-----|-----|-----|
| `z`           | -1  | -1   | -2  | 3   | 1   |
| `s = y+z+1`   | -2  | 1    | -2  | 0   | 3   |
| `x`           | -3  | 2    | -1  | 2   | 0   |
| `x + y`       | -3  | -1   | 1   | 1   | 2   |

Each row is obtained from lower bounds only (`div_eq_lof`): since a principal
divisor has degree zero, lower bounds whose sum is zero are exact.  The lower
bounds come from short bootstraps with the two relations, given here as
explicit polynomial identities in characteristic two.

The combination `div z - 17 div s - 14 div x + 25 div (x + y)` equals
`71·Z - 71·YZ`, so the degree-zero class of `Z - YZ` has order dividing `71`.
-/

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_CertificateDivisors
open Polynomial
open CurveZetaEffectiveDivisors
open RationalPointsN25QuotientF2
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoClosedPointEvaluation
open RationalPointsN25QuotientTwoHyperplaneArtin
open RationalPointsN25QuotientTwoCanonicalDivisor
open RationalPointsN25QuotientTwoConormal RationalPointsN25QuotientWeil
open RationalPointsN25QuotientTwoClosedPointPartition
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoWOpenOrbitPrimeInjective
open RationalPointsN25QuotientTwoWOpenPrimeSurjective hiding W
open RationalPointsN25QuotientTwoWBoundaryZLocal
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open RationalPointsN25QuotientTwoWBoundaryXLocal
open N25F_ProjectiveDivisorSplit N25F_ProjectivePrincipalDivisor
open N25F_ProjectivePrincipalCoefficients N25F_PrincipalOrderAddition
open N25F_NonBoundaryPrincipalDivisor N25F_ProjectiveDivisorDegree
open N25F_XLocalFractionEmbedding N25F_XBoundaryOrder
open N25F_YZLocalFractionEmbedding N25F_YZBoundaryOrder N25F_ZBoundaryOrder
open N25F_ZChartFractionMap N25F_ZChartWChartEquiv
open N25F_SharpBasis N25F_XChartFractionInjective N25F_XChartFractionMap
open N25F_OrderCalculus
open N25F_RationalPointOrders
local notation "K" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
local notation "F" => algebraMap N25F_NonBoundaryPrincipalDivisor.W K

/-! ## Polynomial identities

Each identity holds modulo `Q`, `C`, `2` and the relation `y u = 1` (resp.
`z u = 1`) defining the local parameter `u`; the coefficients were found by a
division computation and are checked here by `linear_combination`. -/

section Identities
set_option linter.unusedSectionVars false
variable (x y z u : K) (hQ : x * z + x + y ^ 2 + y * z + z = 0)
  (hC : x ^ 2 + x * y * z + x * y + x * z + y * z + z ^ 2 + z = 0) (htwo : (2 : K) = 0)
include hQ hC htwo

theorem yz_E1 (hu : y * u = 1) :
    x * u * (z * u * (1 + u)) = x * u * u * (1 + x * u) + z * u * u * (1 + z * u + u) := by
  linear_combination (u ^ 3) * hC + (-u ^ 2 * x * z - u ^ 2 * x - u ^ 2 * z) * hu +
    (-u ^ 3 * x ^ 2 - u ^ 3 * z ^ 2 - u ^ 3 * z - u ^ 2 * x - u ^ 2 * z) * htwo

theorem yz_E2 (hu : y * u = 1) :
    1 + z * u = x * u * (z * u) + x * u * u + z * u * u := by
  linear_combination (u ^ 2) * hQ + (-u * y - u * z - 1) * hu +
    (-u ^ 2 * x * z - u ^ 2 * x - u ^ 2 * z) * htwo

theorem yz_E3 (hu : y * u = 1) :
    1 + z * u + u = x * u * (z * u) + x * u * u + u * (1 + z * u) := by
  linear_combination (u ^ 2) * hQ + (-u * y - u * z - 1) * hu +
    (-u ^ 2 * x * z - u ^ 2 * x - u ^ 2 * z) * htwo

theorem z_E1 (hu : z * u = 1) :
    x * u * (1 + u) = y * u + y * u * (y * u) + u := by
  linear_combination (u ^ 2) * hQ + (-u * x - u * y - u) * hu +
    (-u ^ 2 * y ^ 2 - u * y - u) * htwo

theorem z_E2 (hu : z * u = 1) :
    u + x * u * (y * u) =
      u * (u + x * u + x * u * (x * u) + y * u) + x * u * (y * u) * u := by
  linear_combination (u ^ 3) * hC +
    (-u ^ 2 * x * y - u ^ 2 * x - u ^ 2 * y - u ^ 2 * z - u ^ 2 - u) * hu +
    (-u ^ 3 * x ^ 2 - u ^ 3 * x * y - u ^ 2 * x - u ^ 2 * y - u ^ 2) * htwo

theorem z_E3 (hu : z * u = 1) :
    (x * u + y * u) * (1 + y * u) = x * u * u + (u + x * u * (y * u)) := by
  linear_combination (u ^ 2) * hQ + (-u * x - u * y - u) * hu + (-u ^ 2 * x - u) * htwo

theorem r_1 : z = x * x + x * y * z + x * y + x * z + y * z + z * z := by
  linear_combination hC + (-x ^ 2 - x * y * z - x * y - x * z - y * z - z ^ 2) * htwo

theorem r_2 : x = x * z + y * y + y * z + z := by
  linear_combination hQ + (-x * z - y ^ 2 - y * z - z) * htwo

theorem p_1 : (x + 1) + z = (x + 1) * z + (y + 1) * z + (y + 1) * (y + 1) := by
  linear_combination hQ + (-x * z - y ^ 2 - y * z - y - z) * htwo

theorem p_2 : (x + 1) + (y + 1) =
    (x + 1) * (x + 1) + (x + 1) * (y + 1) + (x + 1) * (y + 1) * z + z * z := by
  linear_combination hC + (-x ^ 2 - x * y * z - x * y - x * z - x - y * z - z ^ 2 - z) * htwo

theorem p_3 : ((y + 1) + z) * (1 + ((x + 1) + z)) =
    ((x + 1) + (y + 1)) * ((x + 1) + (y + 1)) + (x + 1) * (y + 1) * z := by
  linear_combination hQ + hC +
    (-x ^ 2 - x * y * z - x * y - x * z - 2 * x - y ^ 2 - y * z - y - 1) * htwo

end Identities

theorem unit_mul_left (x y u : K) (hu : y * u = 1) : x = x * u * y := by
  linear_combination (-x) * hu

theorem yz_s (y z u : K) (hu : y * u = 1) : y + z + 1 = y * (1 + z * u + u) := by
  linear_combination (-z - 1) * hu

private theorem ne_zero_of_ordAt {A : fullClosedPointGrading25Two.Atom} {f : K} {a : ℤ}
    (h : ordAt A f = a) (ha : a ≠ 0) : f ≠ 0 := by
  rintro rfl
  apply ha
  rw [← h]
  unfold ordAt
  simp

/-- Multiply two lower bounds and weaken to a stated bound. -/
private theorem mulc (A : fullClosedPointGrading25Two.Atom) {f g : K} {a b : ℤ} (c : ℤ)
    (hf : Ge A f a) (hg : Ge A g b) (h : c ≤ a + b) : Ge A (f * g) c :=
  (hf.mul A hg).mono A h

/-! ## The point `YZ`

With `u = 1/y` (order one), `x' = x u` and `z' = z u` (a unit), the relations
give `ord x' ≥ 1`, then `ord (1 + z') ≥ 1`, and finally `ord x' ≥ 3` by
comparing both sides of the cubic once more. -/

set_option maxHeartbeats 1000000 in
private theorem yz_core (A : fullClosedPointGrading25Two.Atom) (x y z u : K)
    (hQ : x * z + x + y ^ 2 + y * z + z = 0)
    (hC : x ^ 2 + x * y * z + x * y + x * z + y * z + z ^ 2 + z = 0) (htwo : (2 : K) = 0)
    (hu : y * u = 1) (hz : z ≠ 0) (hu0 : u ≠ 0) (hou : ordAt A u = 1) (hoz : ordAt A z = -1)
    (hgx : Ge A x (-1)) (hgy : Ge A y (-1)) :
    Ge A x 2 ∧ Ge A (y + z + 1) 1 := by
  have hgu : Ge A u 1 := ge_of_eq A hou
  have hx' : Ge A (x * u) 0 := mulc A 0 hgx hgu (by omega)
  have hz'0 : z * u ≠ 0 := mul_ne_zero hz hu0
  have hoz' : ordAt A (z * u) = 0 := by rw [ordAt_mul A hz hu0, hoz, hou]; norm_num
  have hgz' : Ge A (z * u) 0 := ge_of_eq A hoz'
  obtain ⟨h1u0, ho1u⟩ := ordAt_one_add A hgu
  have h1x' : Ge A (1 + x * u) 0 := (ge_one_zero A).add A hx'
  have h1zu : Ge A (1 + z * u + u) 0 :=
    ((ge_one_zero A).add A hgz').add A (hgu.mono A (by omega))
  have hc0 : z * u * (1 + u) ≠ 0 := mul_ne_zero hz'0 h1u0
  have hoc : ordAt A (z * u * (1 + u)) = 0 := by
    rw [ordAt_mul A hz'0 h1u0, hoz', ho1u]; norm_num
  have E1 := yz_E1 x y z u hQ hC htwo hu
  have E2 := yz_E2 x y z u hQ hC htwo hu
  have E3 := yz_E3 x y z u hQ hC htwo hu
  -- `ord x' ≥ 1`
  have hx1 : Ge A (x * u) 1 := by
    have hL : Ge A (x * u * (z * u * (1 + u))) 1 := by
      rw [E1]
      exact Ge.add A (mulc A 1 (mulc A 1 hx' hgu (by omega)) h1x' (by omega))
        (mulc A 1 (mulc A 1 hgz' hgu (by omega)) h1zu (by omega))
    have := hL.cancel A hc0
    rwa [hoc, sub_zero] at this
  -- `ord (1 + z') ≥ 1`
  have h1z : Ge A (1 + z * u) 1 := by
    rw [E2]
    exact ((mulc A 1 hx1 hgz' (by omega)).add A (mulc A 1 hx1 hgu (by omega))).add A
      (mulc A 1 hgz' hgu (by omega))
  -- `ord x' ≥ 3`
  have hx3 : Ge A (x * u) 3 := by
    by_cases hx'0 : x * u = 0
    · exact Or.inl hx'0
    right
    obtain ⟨m, hm⟩ : ∃ m, ordAt A (x * u) = m := ⟨_, rfl⟩
    rw [hm]
    by_contra hlt
    have hxm : Ge A (x * u) m := ge_of_eq A hm
    have hm1 : 1 ≤ m := hm ▸ hx1.le A hx'0
    have h3 : Ge A (1 + z * u + u) m := by
      rw [E3]
      exact ((mulc A m hxm hgz' (by omega)).add A (mulc A m hxm hgu (by omega))).add A
        (mulc A m hgu h1z (by omega))
    have hL : Ge A (x * u * (z * u * (1 + u))) (m + 1) := by
      rw [E1]
      exact Ge.add A (mulc A (m + 1) (mulc A (m + 1) hxm hgu (by omega)) h1x' (by omega))
        (mulc A (m + 1) (mulc A 1 hgz' hgu (by omega)) h3 (by omega))
    have := (hL.cancel A hc0).le A hx'0
    rw [hoc, hm] at this
    omega
  have h3 : Ge A (1 + z * u + u) 2 := by
    rw [E3]
    exact ((mulc A 2 hx3 hgz' (by omega)).add A (mulc A 2 hx3 hgu (by omega))).add A
      (mulc A 2 hgu h1z (by omega))
  have hx : x = x * u * y := unit_mul_left x y u hu
  have hs : y + z + 1 = y * (1 + z * u + u) := yz_s y z u hu
  refine ⟨?_, ?_⟩
  · rw [hx]; exact mulc A 2 hx3 hgy (by omega)
  · rw [hs]; exact mulc A 1 hgy h3 (by omega)

theorem yz_bounds : Ge atomYZ (F qx) 2 ∧ Ge atomYZ (F qy + F qz + 1) 1 := by
  have hy : F qy ≠ 0 := ne_zero_of_ordAt atomYZ_qy (by norm_num)
  have hz : F qz ≠ 0 := ne_zero_of_ordAt atomYZ_qz (by norm_num)
  exact yz_core atomYZ _ _ _ _ k_quadric k_cubic k_two_eq_zero (mul_inv_cancel₀ hy) hz
    (inv_ne_zero hy) (by rw [ordAt_inv _ hy, atomYZ_qy]; norm_num) atomYZ_qz atomYZ_qx
    (ge_of_eq _ atomYZ_qy)

/-! ## The point `Z`

With `u = 1/z` (order two), `a = x u` (integral) and `b = y u` (order at
least one), the relations give `ord a ≥ 1`, `ord (u + a b) ≥ 3` and
`ord (a + b) ≥ 3`. -/

private theorem z_core (A : fullClosedPointGrading25Two.Atom) (x y z u : K)
    (hQ : x * z + x + y ^ 2 + y * z + z = 0)
    (hC : x ^ 2 + x * y * z + x * y + x * z + y * z + z ^ 2 + z = 0) (htwo : (2 : K) = 0)
    (hu : z * u = 1) (hou : ordAt A u = 2) (hgz : Ge A z (-2))
    (hb : Ge A (y * u) 1) :
    Ge A x (-1) ∧ Ge A (x + y) 1 ∧ Ge A y (-1) := by
  have hgu : Ge A u 2 := ge_of_eq A hou
  obtain ⟨h1u0, ho1u⟩ := ordAt_one_add A (hgu.mono A (by omega))
  obtain ⟨h1b0, ho1b⟩ := ordAt_one_add A hb
  have ha1 : Ge A (x * u) 1 := by
    have hL : Ge A (x * u * (1 + u)) 1 := by
      rw [z_E1 x y z u hQ hC htwo hu]
      exact (hb.add A (mulc A 1 hb hb (by omega))).add A (hgu.mono A (by omega))
    have := hL.cancel A h1u0
    rwa [ho1u, sub_zero] at this
  have hub : Ge A (u + x * u * (y * u)) 3 := by
    rw [z_E2 x y z u hQ hC htwo hu]
    have hin : Ge A (u + x * u + x * u * (x * u) + y * u) 1 :=
      (((hgu.mono A (by omega)).add A ha1).add A (mulc A 1 ha1 ha1 (by omega))).add A hb
    exact (mulc A 3 hgu hin (by omega)).add A (mulc A 3 (mulc A 2 ha1 hb (by omega)) hgu (by omega))
  have hab : Ge A (x * u + y * u) 3 := by
    have hL : Ge A ((x * u + y * u) * (1 + y * u)) 3 := by
      rw [z_E3 x y z u hQ hC htwo hu]
      exact (mulc A 3 ha1 hgu (by omega)).add A hub
    have := hL.cancel A h1b0
    rwa [ho1b, sub_zero] at this
  have hx : x = x * u * z := by linear_combination (-x) * hu
  have hxy : x + y = (x * u + y * u) * z := by linear_combination (-x - y) * hu
  have hy : y = y * u * z := by linear_combination (-y) * hu
  refine ⟨?_, ?_, ?_⟩
  · rw [hx]; exact mulc A (-1) ha1 hgz (by omega)
  · rw [hxy]; exact mulc A 1 hab hgz (by omega)
  · rw [hy]; exact mulc A (-1) hb hgz (by omega)

theorem z_bounds : Ge atomZ (F qx) (-1) ∧ Ge atomZ (F qx + F qy) 1 ∧
    Ge atomZ (F qy) (-1) := by
  have hz : F qz ≠ 0 := ne_zero_of_ordAt atomZ_qz (by norm_num)
  exact z_core atomZ _ _ _ _ k_quadric k_cubic k_two_eq_zero (mul_inv_cancel₀ hz)
    (by rw [ordAt_inv _ hz, atomZ_qz]; norm_num) (ge_of_eq _ atomZ_qz) (by simpa [div_eq_mul_inv] using atomZ_y)

/-! ## The point `R = [0:0:0:1]`

Here `x, y, z` all vanish; the cubic gives `ord z ≥ 2`, the quadric then
`ord x ≥ 2`, and the cubic again `ord z ≥ 3`. -/

private theorem r_core (A : fullClosedPointGrading25Two.Atom) (x y z : K)
    (hQ : x * z + x + y ^ 2 + y * z + z = 0)
    (hC : x ^ 2 + x * y * z + x * y + x * z + y * z + z ^ 2 + z = 0) (htwo : (2 : K) = 0)
    (hx : Ge A x 1) (hy : Ge A y 1) (hz : Ge A z 1) :
    Ge A x 2 ∧ Ge A z 3 := by
  have hz2 : Ge A z 2 := by
    rw [r_1 x y z hQ hC htwo]
    exact (((((mulc A 2 hx hx (by omega)).add A
      (mulc A 2 (mulc A 2 hx hy (by omega)) hz (by omega))).add A
      (mulc A 2 hx hy (by omega))).add A (mulc A 2 hx hz (by omega))).add A
      (mulc A 2 hy hz (by omega))).add A (mulc A 2 hz hz (by omega))
  have hx2 : Ge A x 2 := by
    rw [r_2 x y z hQ hC htwo]
    exact (((mulc A 2 hx hz2 (by omega)).add A (mulc A 2 hy hy (by omega))).add A
      (mulc A 2 hy hz2 (by omega))).add A hz2
  refine ⟨hx2, ?_⟩
  rw [r_1 x y z hQ hC htwo]
  exact (((((mulc A 3 hx2 hx2 (by omega)).add A
    (mulc A 3 (mulc A 3 hx2 hy (by omega)) hz2 (by omega))).add A
    (mulc A 3 hx2 hy (by omega))).add A (mulc A 3 hx2 hz2 (by omega))).add A
    (mulc A 3 hy hz2 (by omega))).add A (mulc A 3 hz2 hz2 (by omega))

theorem r_bounds : Ge atomR (F qx) 2 ∧ Ge atomR (F qz) 3 :=
  r_core atomR _ _ _ k_quadric k_cubic k_two_eq_zero (ge_atomR_of_eval qx originEval_qx)
    (ge_atomR_of_eval qy originEval_qy) (ge_atomR_of_eval qz originEval_qz)

/-! ## The point `P = [1:1:0:1]`

Here `A = x + 1`, `B = y + 1` and `z` vanish; the quadric gives
`ord (A + z) ≥ 2`, the cubic `ord (A + B) ≥ 2`, and their sum
`ord (B + z) ≥ 3`, where `B + z = s`. -/

private theorem p_core (P : fullClosedPointGrading25Two.Atom) (x y z : K)
    (hQ : x * z + x + y ^ 2 + y * z + z = 0)
    (hC : x ^ 2 + x * y * z + x * y + x * z + y * z + z ^ 2 + z = 0) (htwo : (2 : K) = 0)
    (hA : Ge P (x + 1) 1) (hB : Ge P (y + 1) 1) (hz : Ge P z 1) :
    Ge P (x + y) 2 ∧ Ge P (y + z + 1) 3 := by
  have hAz : Ge P ((x + 1) + z) 2 := by
    rw [p_1 x y z hQ hC htwo]
    exact ((mulc P 2 hA hz (by omega)).add P (mulc P 2 hB hz (by omega))).add P
      (mulc P 2 hB hB (by omega))
  have hAB : Ge P ((x + 1) + (y + 1)) 2 := by
    rw [p_2 x y z hQ hC htwo]
    exact (((mulc P 2 hA hA (by omega)).add P (mulc P 2 hA hB (by omega))).add P
      (mulc P 2 (mulc P 2 hA hB (by omega)) hz (by omega))).add P (mulc P 2 hz hz (by omega))
  obtain ⟨h10, ho1⟩ := ordAt_one_add P (hAz.mono P (by omega))
  have hBz : Ge P ((y + 1) + z) 3 := by
    have hL : Ge P (((y + 1) + z) * (1 + ((x + 1) + z))) 3 := by
      rw [p_3 x y z hQ hC htwo]
      exact (mulc P 3 hAB hAB (by omega)).add P
        (mulc P 3 (mulc P 2 hA hB (by omega)) hz (by omega))
    have := hL.cancel P h10
    rwa [ho1, sub_zero] at this
  have h1 : x + y = (x + 1) + (y + 1) := by linear_combination (-1 : K) * htwo
  have h2 : y + z + 1 = (y + 1) + z := by ring
  exact ⟨h1 ▸ hAB, h2 ▸ hBz⟩

theorem p_bounds : Ge atomP (F qx + F qy) 2 ∧ Ge atomP (F qy + F qz + 1) 3 := by
  have hA : Ge atomP (F qx + 1) 1 := by
    have := ge_atomP_of_eval (qx + 1) (by rw [map_add, map_one, binaryPointEval_qx]; decide)
    simpa using this
  have hB : Ge atomP (F qy + 1) 1 := by
    have := ge_atomP_of_eval (qy + 1) (by rw [map_add, map_one, binaryPointEval_qy]; decide)
    simpa using this
  exact p_core atomP _ _ _ k_quadric k_cubic k_two_eq_zero hA hB
    (ge_atomP_of_eval qz binaryPointEval_qz)

/-! ## The four exact divisors -/

theorem qz_ne : F qz ≠ 0 := ne_zero_of_ordAt atomZ_qz (by norm_num)
theorem qx_ne : F qx ≠ 0 := ne_zero_of_ordAt atomX_qx (by norm_num)

theorem s_ne : F (qy + qz + 1) ≠ 0 := by
  rw [map_add, map_add, map_one, add_assoc]
  exact (ordAt_add_of_lt atomX (ne_zero_of_ordAt atomX_qy (by norm_num)) atomX_qy
    ((ge_of_eq _ atomX_qz).add _ ((ge_one_zero _).mono _ (by norm_num)))).1

theorem xy_ne : F (qx + qy) ≠ 0 := by
  rw [map_add]
  exact (ordAt_add_of_lt atomX qx_ne atomX_qx ((ge_of_eq _ atomX_qy).mono _ (by norm_num))).1

theorem div_qz : projectivePrincipalDivisor (Additive.ofMul (Units.mk0 (F qz) qz_ne)) =
    lof (-1) (-1) (-2) 3 1 :=
  div_eq_lof qz qz_ne _ _ _ _ _ (by norm_num) (ge_of_eq _ atomX_qz) (ge_of_eq _ atomYZ_qz)
    (ge_of_eq _ atomZ_qz) r_bounds.2 (ge_atomP_of_eval qz binaryPointEval_qz)

theorem div_s : projectivePrincipalDivisor (Additive.ofMul (Units.mk0 (F (qy + qz + 1)) s_ne)) =
    lof (-2) 1 (-2) 0 3 := by
  have hF : F (qy + qz + 1) = F qy + F qz + 1 := by simp
  refine div_eq_lof _ s_ne _ _ _ _ _ (by norm_num) ?_ ?_ ?_ ?_ ?_
  · rw [hF]
    exact ((ge_of_eq _ atomX_qy).add _ ((ge_of_eq _ atomX_qz).mono _ (by norm_num))).add _
      ((ge_one_zero _).mono _ (by norm_num))
  · rw [hF]; exact yz_bounds.2
  · rw [hF]
    exact ((z_bounds.2.2.mono _ (by norm_num)).add _ (ge_of_eq _ atomZ_qz)).add _
      ((ge_one_zero _).mono _ (by norm_num))
  · exact (ge_nonBoundary nbR _).1
  · rw [hF]; exact p_bounds.2

theorem div_qx : projectivePrincipalDivisor (Additive.ofMul (Units.mk0 (F qx) qx_ne)) =
    lof (-3) 2 (-1) 2 0 :=
  div_eq_lof qx qx_ne _ _ _ _ _ (by norm_num) (ge_of_eq _ atomX_qx) yz_bounds.1 z_bounds.1
    r_bounds.1 (ge_nonBoundary nbP _).1

theorem div_xy : projectivePrincipalDivisor (Additive.ofMul (Units.mk0 (F (qx + qy)) xy_ne)) =
    lof (-3) (-1) 1 1 2 := by
  have hF : F (qx + qy) = F qx + F qy := map_add _ _ _
  refine div_eq_lof _ xy_ne _ _ _ _ _ (by norm_num) ?_ ?_ ?_ ?_ ?_
  · rw [hF]
    exact (ge_of_eq _ atomX_qx).add _ ((ge_of_eq _ atomX_qy).mono _ (by norm_num))
  · rw [hF]; exact atomYZ_qx.add _ (ge_of_eq _ atomYZ_qy)
  · rw [hF]; exact z_bounds.2.1
  · exact ge_atomR_of_eval _ (by rw [map_add, originEval_qx, originEval_qy, add_zero])
  · rw [hF]; exact p_bounds.1

/-! ## The certificate -/

theorem lof_add (a b c d e a' b' c' d' e' : ℤ) :
    lof a b c d e + lof a' b' c' d' e' = lof (a + a') (b + b') (c + c') (d + d') (e + e') := by
  simp only [lof, Finsupp.single_add]
  abel

theorem lof_zsmul (n a b c d e : ℤ) :
    n • lof a b c d e = lof (n * a) (n * b) (n * c) (n * d) (n * e) := by
  simp only [lof, smul_add, Finsupp.smul_single, smul_eq_mul]

/-- The unit `z · s⁻¹⁷ · x⁻¹⁴ · (x + y)²⁵` of the function field. -/
def certificateUnit : Kˣ :=
  Units.mk0 (F qz) qz_ne * Units.mk0 (F (qy + qz + 1)) s_ne ^ (-17 : ℤ) *
    Units.mk0 (F qx) qx_ne ^ (-14 : ℤ) * Units.mk0 (F (qx + qy)) xy_ne ^ (25 : ℤ)

/-- **The certificate.**  `div (z s⁻¹⁷ x⁻¹⁴ (x+y)²⁵) = 71·Z - 71·YZ`. -/
theorem div_certificateUnit :
    projectivePrincipalDivisor (Additive.ofMul certificateUnit) = lof 0 (-71) 71 0 0 := by
  rw [certificateUnit, ofMul_mul, ofMul_mul, ofMul_mul, ofMul_zpow, ofMul_zpow, ofMul_zpow,
    map_add, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, div_qz, div_s, div_qx, div_xy,
    lof_zsmul, lof_zsmul, lof_zsmul, lof_add, lof_add, lof_add]
  norm_num

end MazurProof.N25F_CertificateDivisors
