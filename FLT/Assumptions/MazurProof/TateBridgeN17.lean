import FLT.Assumptions.MazurProof.TateBridgeN17Data
import FLT.Assumptions.MazurProof.RationalPointsX017

/-!
# Tate bridge for p=17: explicit map to X₀(17)

From Tate parameters (b,c) with F17(b,c)=0 and b≠0, constructs a
rational point on X₀(17) = 17a1: y²+xy+y = x³-x²-x-14.

The map is the diamond trace: X₁(17) → X₀(17), computed via the
⟨3⟩-diamond operator which generates (Z/17Z)*/±1 (order 8).
The polynomials A₁₇, B₁₇ and the certificate C₁₇ were computed by
CRT interpolation and verified symbolically.
-/

namespace MazurProof.TateBridgeN17

open TateNFDivision

noncomputable section

def Xnum17 (b c : ℚ) : ℚ := A17 b c - 4 * c ^ 28

def Ynum17 (b c : ℚ) : ℚ := c * A17 b c - B17 b c - c ^ 29

def mapX17 (b c : ℚ) : ℚ := Xnum17 b c / c ^ 28

def mapY17 (b c : ℚ) : ℚ := Ynum17 b c / c ^ 29

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 4096 in
theorem curve_identity_17 (b c : ℚ) :
    c ^ 26 * (Ynum17 b c) ^ 2 + c ^ 27 * (Xnum17 b c) * (Ynum17 b c)
    + c ^ 55 * (Ynum17 b c) - (Xnum17 b c) ^ 3
    + c ^ 28 * (Xnum17 b c) ^ 2 + c ^ 56 * (Xnum17 b c) + 14 * c ^ 84
    = F17 b c * C17 b c := by
  simp only [Xnum17, Ynum17, A17, B17, F17, C17, C17_lo, C17_hi, F5, F6, F7, F8, F9]
  ring

theorem c_ne_zero_of_F17 (b c : ℚ) (hb : b ≠ 0) (hF : F17 b c = 0) :
    c ≠ 0 := by
  intro hc; subst hc
  simp only [F17, F5, F6, F7, F8, F9] at hF
  have : b ^ 12 = 0 := by nlinarith
  exact hb (pow_eq_zero_iff (n := 12) (by norm_num) |>.mp this)

theorem on_X017_of_F17 (b c : ℚ) (hc : c ≠ 0) (hF : F17 b c = 0) :
    (mapY17 b c) ^ 2 + (mapX17 b c) * (mapY17 b c) + (mapY17 b c)
    = (mapX17 b c) ^ 3 - (mapX17 b c) ^ 2 - (mapX17 b c) - 14 := by
  have h := curve_identity_17 b c
  rw [hF, zero_mul] at h
  unfold mapX17 mapY17
  field_simp [hc]
  nlinarith

theorem mapX17_mapY17_classified (b c : ℚ) (hb : b ≠ 0) (hF : F17 b c = 0) :
    (mapX17 b c = 7 ∧ mapY17 b c = 13) ∨
    (mapX17 b c = 11 / 4 ∧ mapY17 b c = -15 / 8) ∨
    (mapX17 b c = 7 ∧ mapY17 b c = -21) := by
  have hc := c_ne_zero_of_F17 b c hb hF
  have hcurve := on_X017_of_F17 b c hc hF
  have hOnE : RationalPointsX017.OnE17 (mapX17 b c) (mapY17 b c) := by
    unfold RationalPointsX017.OnE17
    linarith
  exact RationalPointsX017.affine_rational_points hOnE

end

end MazurProof.TateBridgeN17
