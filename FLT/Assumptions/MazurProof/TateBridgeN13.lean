import FLT.Assumptions.MazurProof.TateNFDivision

/-!
# Tate bridge for order 13: explicit map to the optimized X₁(13) model

From the Tate parameters (b,c) with F13(b,c)=0 and b≠0, we construct
a rational point on the optimized model of X₁(13):

  v² + (u³+u²+1)v = u² + u

using the explicit rational functions u = (b-c)(b-c-c²)/(b²-bc-c³)
and v = -(b²-bc-c³)/(c(b-c-c²)).

We then show u ≠ 0 and u ≠ -1, ruling out the cusps x = 0 and x = -1
on the sextic model y² = x⁶+4x⁵+6x⁴+2x³+x²+2x+1.
-/

namespace MazurProof.TateBridgeN13

open TateNFDivision

noncomputable section

def tateP (b c : ℚ) : ℚ := b - c
def tateQ (b c : ℚ) : ℚ := b - c - c^2
def tateG (b c : ℚ) : ℚ := b^2 - b*c - c^3

def mapU (b c : ℚ) : ℚ := tateP b c * tateQ b c / tateG b c
def mapV (b c : ℚ) : ℚ := -tateG b c / (c * tateQ b c)

def x1_13_opt_equation (u v : ℚ) : Prop :=
  v^2 + (u^3 + u^2 + 1) * v = u^2 + u

theorem F13_at_c_eq_zero (b : ℚ) : F13 b 0 = -b^7 := by
  unfold F13 F5 F6 F7 F8
  ring

theorem F13_at_b_eq_c (c : ℚ) : F13 c c = c^11 := by
  unfold F13 F5 F6 F7 F8
  ring

theorem F13_at_b_eq_c_plus_c_sq (c : ℚ) : F13 (c + c^2) c = -c^14 := by
  unfold F13 F5 F6 F7 F8
  ring

theorem bezout_G_F8 (b c : ℚ) :
    (2*(c+1)*b - c*(c^2+1)) * tateG b c +
    (-(c+1)*b - c^2) * F8 b c = c^6 := by
  unfold tateG F8
  ring

theorem F13_factored (b c : ℚ) :
    F13 b c = -(tateP b c) * (tateG b c)^3 +
      b * c * F8 b c * (tateQ b c)^3 := by
  unfold F13 F5 F6 F7 F8 tateP tateG tateQ
  ring

theorem mapU_add_one (b c : ℚ) (hG : tateG b c ≠ 0) :
    mapU b c + 1 = F8 b c / tateG b c := by
  unfold mapU tateP tateQ tateG F8
  field_simp [hG]
  ring

theorem opt_curve_identity (b c : ℚ)
    (hc : c ≠ 0) (hq : tateQ b c ≠ 0) (hG : tateG b c ≠ 0) :
    (mapV b c)^2 + ((mapU b c)^3 + (mapU b c)^2 + 1) * mapV b c
      - (mapU b c)^2 - mapU b c =
    -(tateP b c) * F13 b c / (c^2 * (tateQ b c)^2 * (tateG b c)^2) := by
  unfold mapU mapV tateP tateQ tateG F13 F5 F6 F7 F8
  field_simp [hc, hq, hG]
  ring

theorem c_ne_zero_of_F13 (b c : ℚ) (hb : b ≠ 0) (hF : F13 b c = 0) :
    c ≠ 0 := by
  intro hc; subst hc
  rw [F13_at_c_eq_zero] at hF
  have : b^7 = 0 := by linarith
  exact hb (pow_eq_zero_iff (n := 7) (by norm_num) |>.mp this)

theorem p_ne_zero_of_F13 (b c : ℚ) (hb : b ≠ 0) (hF : F13 b c = 0) :
    tateP b c ≠ 0 := by
  intro hp
  have hbc : b = c := sub_eq_zero.mp hp
  have : F13 c c = 0 := hbc ▸ hF
  rw [F13_at_b_eq_c] at this
  have hc : c = 0 := pow_eq_zero_iff (n := 11) (by norm_num) |>.mp this
  exact hb (hbc ▸ hc ▸ rfl)

theorem q_ne_zero_of_F13 (b c : ℚ) (hb : b ≠ 0) (hF : F13 b c = 0) :
    tateQ b c ≠ 0 := by
  have hc := c_ne_zero_of_F13 b c hb hF
  intro hq
  have hbc : b = c + c^2 := by unfold tateQ at hq; linarith
  have : F13 (c + c^2) c = 0 := hbc ▸ hF
  rw [F13_at_b_eq_c_plus_c_sq] at this
  exact hc (pow_eq_zero_iff (n := 14) (by norm_num) |>.mp (neg_eq_zero.mp this))

theorem G_ne_zero_of_F13 (b c : ℚ) (hb : b ≠ 0) (hF : F13 b c = 0) :
    tateG b c ≠ 0 := by
  intro hG0
  have hc := c_ne_zero_of_F13 b c hb hF
  have hq := q_ne_zero_of_F13 b c hb hF
  have hfac := F13_factored b c
  rw [hF, hG0] at hfac
  simp at hfac
  have hF8 : F8 b c = 0 := by
    rcases hfac with ((h | h) | h) | h
    · exact absurd h hb
    · exact absurd h hc
    · exact h
    · exact absurd h hq
  have hbez := bezout_G_F8 b c
  rw [hG0, hF8] at hbez
  simp at hbez
  exact hc (pow_eq_zero_iff (n := 6) (by norm_num) |>.mp hbez.symm)

theorem F8_ne_zero_of_F13 (b c : ℚ) (hb : b ≠ 0) (hF : F13 b c = 0) :
    F8 b c ≠ 0 := by
  intro hF8
  have hp := p_ne_zero_of_F13 b c hb hF
  have hG := G_ne_zero_of_F13 b c hb hF
  have hfac := F13_factored b c
  rw [hF, hF8] at hfac
  simp at hfac
  rcases hfac with h | h
  · exact hp h
  · exact hG h

theorem mapU_ne_zero (b c : ℚ) (hb : b ≠ 0) (hF : F13 b c = 0) :
    mapU b c ≠ 0 := by
  unfold mapU
  have hp := p_ne_zero_of_F13 b c hb hF
  have hq := q_ne_zero_of_F13 b c hb hF
  have hG := G_ne_zero_of_F13 b c hb hF
  exact div_ne_zero (mul_ne_zero hp hq) hG

theorem mapU_ne_neg_one (b c : ℚ) (hb : b ≠ 0) (hF : F13 b c = 0) :
    mapU b c ≠ -1 := by
  have hG := G_ne_zero_of_F13 b c hb hF
  have hF8 := F8_ne_zero_of_F13 b c hb hF
  rw [ne_eq, ← add_eq_zero_iff_eq_neg, mapU_add_one b c hG]
  exact div_ne_zero hF8 hG

theorem opt_curve_on_F13 (b c : ℚ) (hb : b ≠ 0) (hF : F13 b c = 0) :
    x1_13_opt_equation (mapU b c) (mapV b c) := by
  have hc := c_ne_zero_of_F13 b c hb hF
  have hq := q_ne_zero_of_F13 b c hb hF
  have hG := G_ne_zero_of_F13 b c hb hF
  unfold x1_13_opt_equation
  have := opt_curve_identity b c hc hq hG
  rw [hF] at this
  simp at this
  linarith

end

end MazurProof.TateBridgeN13
