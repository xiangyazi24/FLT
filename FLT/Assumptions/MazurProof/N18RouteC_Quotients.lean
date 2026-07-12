import FLT.Assumptions.MazurProof.N18RouteC_Split

/-!
# Explicit quotient maps for N18 Route C

This module turns the homogeneous splitting identities into affine-open and
denominator-free projective quotient certificates.  It deliberately stops
before the structural smooth-projective-curve adapter: every statement here
is an exact identity in the fixed cubic field.
-/

namespace MazurProof.N18RouteC.Quotients

noncomputable section

set_option maxRecDepth 100000

@[simp]
theorem a_pow_recurrence (n : ℕ) :
    a ^ n.succ.succ.succ = 3 * a ^ n.succ + a ^ n := by
  change a ^ (n + 3) = 3 * a ^ (n + 1) + a ^ n
  rw [pow_add, a_cubic, pow_succ]
  ring

theorem a_pow_fifteen : a ^ 15 = 3 * a ^ 13 + a ^ 12 := by
  simpa using a_pow_recurrence 12

theorem a_pow_sixteen : a ^ 16 = 3 * a ^ 14 + a ^ 13 := by
  simpa using a_pow_recurrence 13

theorem a_pow_seventeen : a ^ 17 = 3 * a ^ 15 + a ^ 14 := by
  simpa using a_pow_recurrence 14

theorem a_pow_eighteen : a ^ 18 = 3 * a ^ 16 + a ^ 15 := by
  simpa using a_pow_recurrence 15

theorem a_pow_nineteen : a ^ 19 = 3 * a ^ 17 + a ^ 16 := by
  simpa using a_pow_recurrence 16

theorem a_pow_twenty : a ^ 20 = 3 * a ^ 18 + a ^ 17 := by
  simpa using a_pow_recurrence 17

theorem a_pow_twenty_one : a ^ 21 = 3 * a ^ 19 + a ^ 18 := by
  simpa using a_pow_recurrence 18

theorem a_pow_twenty_two : a ^ 22 = 3 * a ^ 20 + a ^ 19 := by
  simpa using a_pow_recurrence 19

theorem a_pow_twenty_three : a ^ 23 = 3 * a ^ 21 + a ^ 20 := by
  simpa using a_pow_recurrence 20

theorem a_pow_twenty_four : a ^ 24 = 3 * a ^ 22 + a ^ 21 := by
  simpa using a_pow_recurrence 21

theorem a_pow_twenty_five : a ^ 25 = 3 * a ^ 23 + a ^ 22 := by
  simpa using a_pow_recurrence 22

theorem a_pow_twenty_six : a ^ 26 = 3 * a ^ 24 + a ^ 23 := by
  simpa using a_pow_recurrence 23

theorem a_pow_twenty_seven : a ^ 27 = 3 * a ^ 25 + a ^ 24 := by
  simpa using a_pow_recurrence 24

theorem a_pow_twenty_eight : a ^ 28 = 3 * a ^ 26 + a ^ 25 := by
  simpa using a_pow_recurrence 25

theorem a_pow_twenty_nine : a ^ 29 = 3 * a ^ 27 + a ^ 26 := by
  simpa using a_pow_recurrence 26

theorem a_pow_thirty : a ^ 30 = 3 * a ^ 28 + a ^ 27 := by
  simpa using a_pow_recurrence 27

local macro "n18q_ring" : tactic =>
  `(tactic|
    (ring_nf <;>
     simp only [a_pow_thirty, a_pow_twenty_nine, a_pow_twenty_eight,
       a_pow_twenty_seven, a_pow_twenty_six, a_pow_twenty_five,
       a_pow_twenty_four, a_pow_twenty_three, a_pow_twenty_two,
       a_pow_twenty_one, a_pow_twenty, a_pow_nineteen, a_pow_eighteen,
       a_pow_seventeen, a_pow_sixteen, a_pow_fifteen, a_pow_fourteen,
       a_pow_thirteen, a_pow_twelve, a_pow_eleven, a_pow_ten,
       a_pow_nine, a_pow_eight, a_pow_seven, a_pow_six, a_pow_five,
       a_pow_four, a_cubic] <;>
     ring))

/-! ## The affine involution on its regular chart -/

structure CAffinePoint where
  x : L
  y : L
  onCurve : y ^ 2 = curveF x

@[ext]
theorem CAffinePoint.ext {P Q : CAffinePoint}
    (hx : P.x = Q.x) (hy : P.y = Q.y) : P = Q := by
  cases P
  cases Q
  simp_all

def sigmaX (x : L) : L := (A0 * x - a) / (x - A0)
def sigmaY (x y : L) : L := q0 ^ 3 * y / (x - A0) ^ 3

theorem q0_ne_zero : q0 ≠ 0 := by
  intro hq0
  have hq : a ^ 2 - 1 = 0 := by simpa [q0] using hq0
  have hrel : a ^ 3 - 3 * a - 1 = 0 := by rw [a_cubic]; ring
  have hlin : 2 * a + 1 = 0 := by
    linear_combination a * hq - hrel
  have ha : a = -(1 / 2 : L) := by
    linear_combination (1 / 2 : L) * hlin
  rw [ha] at hq
  norm_num at hq

theorem sigma_den_cleared (x : L) :
    (A0 * x - a) - A0 * (x - A0) = q0 ^ 2 := by
  unfold A0 q0
  n18q_ring

theorem sigma_num_cleared (x : L) :
    A0 * (A0 * x - a) - a * (x - A0) = q0 ^ 2 * x := by
  unfold A0 q0
  n18q_ring

theorem sigmaX_sub_A0 (x : L) (hx : x ≠ A0) :
    sigmaX x - A0 = q0 ^ 2 / (x - A0) := by
  have hd : x - A0 ≠ 0 := sub_ne_zero.mpr hx
  unfold sigmaX
  field_simp [hd]
  exact sigma_den_cleared x

theorem sigmaX_ne_A0 (x : L) (hx : x ≠ A0) : sigmaX x ≠ A0 := by
  rw [← sub_ne_zero, sigmaX_sub_A0 x hx]
  exact div_ne_zero (pow_ne_zero 2 q0_ne_zero) (sub_ne_zero.mpr hx)

theorem sigmaX_involutive (x : L) (hx : x ≠ A0) :
    sigmaX (sigmaX x) = x := by
  have hd : x - A0 ≠ 0 := sub_ne_zero.mpr hx
  have hnum : A0 * sigmaX x - a = q0 ^ 2 * x / (x - A0) := by
    unfold sigmaX
    field_simp [hd]
    simpa only [mul_comm] using sigma_num_cleared x
  change (A0 * sigmaX x - a) / (sigmaX x - A0) = x
  rw [hnum, sigmaX_sub_A0 x hx]
  field_simp [hd, q0_ne_zero]

theorem sigmaY_involutive (x y : L) (hx : x ≠ A0) :
    sigmaY (sigmaX x) (sigmaY x y) = y := by
  have hsub := sigmaX_sub_A0 x hx
  have hd : x - A0 ≠ 0 := sub_ne_zero.mpr hx
  unfold sigmaY
  rw [hsub]
  field_simp [hd, q0_ne_zero] <;> ring

theorem sigma_preserves_f_cleared (x : L) :
    curveFHom (A0 * x - a) (x - A0) = q0 ^ 6 * curveF x := by
  simpa [sigmaXNum, sigmaXDen, curveFHom, curveF] using
    sigma_preserves_homogeneous x 1

theorem curveF_div_identity (N D : L) (hD : D ≠ 0) :
    curveF (N / D) = curveFHom N D / D ^ 6 := by
  unfold curveF curveFHom
  field_simp [hD]

theorem sigma_preserves_curve
    {x y : L} (hx : x ≠ A0) (hC : y ^ 2 = curveF x) :
    (sigmaY x y) ^ 2 = curveF (sigmaX x) := by
  have hd : x - A0 ≠ 0 := sub_ne_zero.mpr hx
  calc
    (sigmaY x y) ^ 2 = q0 ^ 6 * y ^ 2 / (x - A0) ^ 6 := by
      unfold sigmaY
      field_simp [hd]
    _ = q0 ^ 6 * curveF x / (x - A0) ^ 6 := by rw [hC]
    _ = curveFHom (A0 * x - a) (x - A0) / (x - A0) ^ 6 := by
      rw [sigma_preserves_f_cleared]
    _ = curveF ((A0 * x - a) / (x - A0)) :=
      (curveF_div_identity (A0 * x - a) (x - A0) hd).symm
    _ = curveF (sigmaX x) := rfl

def COpenA0 := {P : CAffinePoint // P.x ≠ A0}

def sigmaOpen (P : COpenA0) : COpenA0 :=
  ⟨{ x := sigmaX P.1.x
     y := sigmaY P.1.x P.1.y
     onCurve := sigma_preserves_curve P.2 P.1.onCurve },
   sigmaX_ne_A0 P.1.x P.2⟩

theorem sigmaOpen_involutive : Function.Involutive sigmaOpen := by
  intro P
  apply Subtype.ext
  apply CAffinePoint.ext
  · exact sigmaX_involutive P.1.x P.2
  · exact sigmaY_involutive P.1.x P.1.y P.2

/-! ## Diagonal coordinates -/

def zCoord (x : L) : L := (x - rp) / (x - rm)
def wCoord (x y : L) : L := -8 * q0 ^ 3 * y / (x - rm) ^ 3

theorem rp_ne_rm : rp ≠ rm := by
  apply sub_ne_zero.mp
  rw [rp_sub_rm]
  exact mul_ne_zero (by norm_num) q0_ne_zero

theorem sigma_sub_rp_cleared (x : L) :
    (A0 * x - a) - rp * (x - A0) = -q0 * (x - rp) := by
  simp only [rp, A0, q0]
  n18q_ring

theorem sigma_sub_rm_cleared (x : L) :
    (A0 * x - a) - rm * (x - A0) = q0 * (x - rm) := by
  simp only [rm, A0, q0]
  n18q_ring

theorem sigmaX_sub_rp (x : L) (hxA : x ≠ A0) :
    sigmaX x - rp = -q0 * (x - rp) / (x - A0) := by
  have hdA : x - A0 ≠ 0 := sub_ne_zero.mpr hxA
  unfold sigmaX
  field_simp [hdA]
  convert sigma_sub_rp_cleared x using 1 <;> ring

theorem sigmaX_sub_rm (x : L) (hxA : x ≠ A0) :
    sigmaX x - rm = q0 * (x - rm) / (x - A0) := by
  have hdA : x - A0 ≠ 0 := sub_ne_zero.mpr hxA
  unfold sigmaX
  field_simp [hdA]
  simpa only [mul_comm] using sigma_sub_rm_cleared x

theorem zCoord_sigma
    (x : L) (hxA : x ≠ A0) (hxM : x ≠ rm) :
    zCoord (sigmaX x) = -zCoord x := by
  have hdA : x - A0 ≠ 0 := sub_ne_zero.mpr hxA
  have hdM : x - rm ≠ 0 := sub_ne_zero.mpr hxM
  rw [zCoord, zCoord, sigmaX_sub_rp x hxA, sigmaX_sub_rm x hxA]
  field_simp [hdA, hdM, q0_ne_zero]

theorem wCoord_sigma
    (x y : L) (hxA : x ≠ A0) (hxM : x ≠ rm) :
    wCoord (sigmaX x) (sigmaY x y) = wCoord x y := by
  have hdA : x - A0 ≠ 0 := sub_ne_zero.mpr hxA
  have hdM : x - rm ≠ 0 := sub_ne_zero.mpr hxM
  unfold wCoord
  rw [sigmaX_sub_rm x hxA]
  unfold sigmaY
  field_simp [hdA, hdM, q0_ne_zero]

def tauX (x : L) : L := sigmaX x
def tauY (x y : L) : L := -sigmaY x y

/-! ## Even sextic and the two raw elliptic quotients -/

theorem even_sextic_cleared (x : L) :
    64 * q0 ^ 6 * curveF x =
      c3 * (x - rp) ^ 6 +
      c2 * (x - rp) ^ 4 * (x - rm) ^ 2 +
      c0 * (x - rm) ^ 6 := by
  simp only [curveF, c3, c2, c0, D0, rp, rm, A0, q0]
  n18q_ring

theorem even_sextic_of_curve
    {x y : L} (hC : y ^ 2 = curveF x) (hxM : x ≠ rm) :
    (wCoord x y) ^ 2 =
      c3 * (zCoord x) ^ 6 + c2 * (zCoord x) ^ 4 + c0 := by
  have hdM : x - rm ≠ 0 := sub_ne_zero.mpr hxM
  unfold wCoord zCoord
  field_simp [hdM]
  rw [hC]
  simp only [curveF, c3, c2, c0, D0, rp, rm, A0, q0]
  n18q_ring

def EplusRaw : WeierstrassCurve L where
  a₁ := 0
  a₂ := c2
  a₃ := 0
  a₄ := 0
  a₆ := c0 * c3 ^ 2

def EminusRaw : WeierstrassCurve L where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := c2 * c0
  a₆ := c3 * c0 ^ 2

def wcResidual (W : WeierstrassCurve L) (X Y : L) : L :=
  Y ^ 2 + W.a₁ * X * Y + W.a₃ * Y -
    (X ^ 3 + W.a₂ * X ^ 2 + W.a₄ * X + W.a₆)

def plusRawX (x : L) : L := c3 * (x - rp) ^ 2 / (x - rm) ^ 2
def plusRawY (x y : L) : L := -8 * c3 * q0 ^ 3 * y / (x - rm) ^ 3

def minusRawX (x : L) : L := c0 * (x - rm) ^ 2 / (x - rp) ^ 2
def minusRawY (x y : L) : L := -8 * c0 * q0 ^ 3 * y / (x - rp) ^ 3

theorem plusRaw_on_curve
    {x y : L} (hC : y ^ 2 = curveF x) (hxM : x ≠ rm) :
    wcResidual EplusRaw (plusRawX x) (plusRawY x y) = 0 := by
  have hdM : x - rm ≠ 0 := sub_ne_zero.mpr hxM
  unfold wcResidual EplusRaw plusRawX plusRawY
  field_simp [hdM]
  ring_nf
  rw [hC]
  simp only [curveF, c3, c2, c0, D0, rp, rm, A0, q0]
  n18q_ring

theorem minusRaw_on_curve
    {x y : L} (hC : y ^ 2 = curveF x) (hxP : x ≠ rp) :
    wcResidual EminusRaw (minusRawX x) (minusRawY x y) = 0 := by
  have hdP : x - rp ≠ 0 := sub_ne_zero.mpr hxP
  unfold wcResidual EminusRaw minusRawX minusRawY
  field_simp [hdP]
  ring_nf
  rw [hC]
  simp only [curveF, c3, c2, c0, D0, rp, rm, A0, q0]
  n18q_ring

/-! ## Explicit changes to convenient Weierstrass models -/

/-- The rational companion model used by the split certificate. -/
def EhatConvenient : WeierstrassCurve L where
  a₁ := 1
  a₂ := -1
  a₃ := 1
  a₄ := 25
  a₆ := 1

def alphaPlus : L := (-2 * a ^ 2 - a + 9) / 48
def betaPlus : L := (2 * a ^ 2 + a - 9) / 96
def gammaPlus : L := (4 * a ^ 2 + a - 16) / 192

def plusIsoX (X : L) : L := alphaPlus * X + 3 / 2
def plusIsoY (X Y : L) : L := betaPlus * X + gammaPlus * Y - 5 / 4

def alphaMinus : L := (-2 * a ^ 2 + a + 7) / 16
def betaMinus : L := (2 * a ^ 2 - a - 7) / 32
def gammaMinus : L := (6 * a ^ 2 - 3 * a - 18) / 64

def minusIsoX (X : L) : L := alphaMinus * X + 1 / 4
def minusIsoY (X Y : L) : L := betaMinus * X + gammaMinus * Y - 5 / 8

theorem plus_change_residual (X Y : L) :
    wcResidual E0 (plusIsoX X) (plusIsoY X Y) =
      gammaPlus ^ 2 * wcResidual EplusRaw X Y := by
  unfold wcResidual E0 EplusRaw plusIsoX plusIsoY
  unfold alphaPlus betaPlus gammaPlus c3 c2 c0 D0
  field_simp
  n18q_ring

theorem minus_change_residual (X Y : L) :
    wcResidual EhatConvenient (minusIsoX X) (minusIsoY X Y) =
      gammaMinus ^ 2 * wcResidual EminusRaw X Y := by
  unfold wcResidual EhatConvenient EminusRaw minusIsoX minusIsoY
  unfold alphaMinus betaMinus gammaMinus c3 c2 c0 D0
  field_simp
  n18q_ring

def plusU : L := 4 * a ^ 2 + 8 * a
def plusR : L := -168 * a ^ 2 - 312 * a - 96
def plusS : L := 2 * a ^ 2 + 4 * a
def plusT : L := 1632 * a ^ 2 + 3072 * a + 864

theorem a_ne_zero : a ≠ 0 := by
  intro ha
  have h := a_cubic
  rw [ha] at h
  norm_num at h

theorem a_add_two_ne_zero : a + 2 ≠ 0 := by
  intro h
  have ha : a = -(2 : L) := by linear_combination h
  have hc := a_cubic
  rw [ha] at hc
  norm_num at hc

theorem plusU_ne_zero : plusU ≠ 0 := by
  unfold plusU
  rw [show 4 * a ^ 2 + 8 * a = 4 * a * (a + 2) by ring]
  exact mul_ne_zero (mul_ne_zero (by norm_num) a_ne_zero) a_add_two_ne_zero

def plusUUnit : Lˣ := Units.mk0 plusU plusU_ne_zero

@[simp]
theorem plusUUnit_inv_val : (↑(plusUUnit⁻¹) : L) = plusU⁻¹ := rfl

def plusVC : WeierstrassCurve.VariableChange L :=
  ⟨plusUUnit, plusR, plusS, plusT⟩

theorem plusVC_curve : plusVC • EplusRaw = E0 := by
  rw [WeierstrassCurve.variableChange_def]
  ext <;>
    dsimp only [plusVC, EplusRaw, E0] <;>
    simp only [plusUUnit_inv_val] <;>
    field_simp [plusU_ne_zero] <;>
    simp only [plusU, plusR, plusS, plusT, c3, c2, c0, D0] <;>
    n18q_ring

def minusU : L := (4 * a ^ 2 - 8 * a - 8) / 3
def minusR : L := (-4 * a ^ 2 + 4 * a) / 3
def minusS : L := (2 * a ^ 2 - 4 * a - 4) / 3
def minusT : L := (32 * a ^ 2 - 64 * a - 32) / 3

theorem minusQuadratic_ne_zero : a ^ 2 - 2 * a - 2 ≠ 0 := by
  intro hq
  have hrel : a ^ 3 - 3 * a - 1 = 0 := by rw [a_cubic]; ring
  have hlin : 3 * a + 3 = 0 := by
    linear_combination hrel - a * hq - 2 * hq
  have ha : a = -1 := by
    linear_combination (1 / 3 : L) * hlin
  rw [ha] at hq
  norm_num at hq

theorem minusU_ne_zero : minusU ≠ 0 := by
  unfold minusU
  rw [show 4 * a ^ 2 - 8 * a - 8 =
    4 * (a ^ 2 - 2 * a - 2) by ring]
  exact div_ne_zero
    (mul_ne_zero (by norm_num) minusQuadratic_ne_zero) (by norm_num)

def minusUUnit : Lˣ := Units.mk0 minusU minusU_ne_zero

@[simp]
theorem minusUUnit_inv_val : (↑(minusUUnit⁻¹) : L) = minusU⁻¹ := rfl

def minusVC : WeierstrassCurve.VariableChange L :=
  ⟨minusUUnit, minusR, minusS, minusT⟩

theorem minusVC_curve : minusVC • EminusRaw = EhatConvenient := by
  rw [WeierstrassCurve.variableChange_def]
  ext <;>
    dsimp only [minusVC, EminusRaw, EhatConvenient] <;>
    simp only [minusUUnit_inv_val] <;>
    field_simp [minusU_ne_zero] <;>
    simp only [minusU, minusR, minusS, minusT, c3, c2, c0, D0] <;>
    n18q_ring

/-! ## Denominator-free total quotient certificates -/

def projectiveResidual (W : WeierstrassCurve L) (X Y Z : L) : L :=
  Y ^ 2 * Z + W.a₁ * X * Y * Z + W.a₃ * Y * Z ^ 2 -
    (X ^ 3 + W.a₂ * X ^ 2 * Z + W.a₄ * X * Z ^ 2 + W.a₆ * Z ^ 3)

def qPlusD (x : L) : L := x - rm

def qPlusNX (x : L) : L :=
  alphaPlus * c3 * (x - rp) ^ 2 + (3 / 2 : L) * (x - rm) ^ 2

def qPlusNY (x y : L) : L :=
  betaPlus * c3 * (x - rp) ^ 2 * (x - rm) -
    8 * gammaPlus * c3 * q0 ^ 3 * y -
    (5 / 4 : L) * (x - rm) ^ 3

def qPlusProjective (x y : L) : Fin 3 → L :=
  ![qPlusNX x * qPlusD x, qPlusNY x y, qPlusD x ^ 3]

theorem qPlus_projective_identity
    {x y : L} (hC : y ^ 2 = curveF x) :
    projectiveResidual E0
      (qPlusProjective x y 0)
      (qPlusProjective x y 1)
      (qPlusProjective x y 2) = 0 := by
  change projectiveResidual E0
    (qPlusNX x * qPlusD x) (qPlusNY x y) (qPlusD x ^ 3) = 0
  unfold projectiveResidual qPlusNX qPlusNY qPlusD
  simp only [E0, alphaPlus, betaPlus, gammaPlus, c3, c2, c0, D0,
    rp, rm, A0, q0, curveF]
  field_simp
  ring_nf
  rw [hC]
  simp only [curveF]
  n18q_ring

def qMinusD (x : L) : L := x - rp

def qMinusNX (x : L) : L :=
  alphaMinus * c0 * (x - rm) ^ 2 + (1 / 4 : L) * (x - rp) ^ 2

def qMinusNY (x y : L) : L :=
  betaMinus * c0 * (x - rm) ^ 2 * (x - rp) -
    8 * gammaMinus * c0 * q0 ^ 3 * y -
    (5 / 8 : L) * (x - rp) ^ 3

def qMinusProjective (x y : L) : Fin 3 → L :=
  ![qMinusNX x * qMinusD x, qMinusNY x y, qMinusD x ^ 3]

theorem qMinus_projective_identity
    {x y : L} (hC : y ^ 2 = curveF x) :
    projectiveResidual EhatConvenient
      (qMinusProjective x y 0)
      (qMinusProjective x y 1)
      (qMinusProjective x y 2) = 0 := by
  change projectiveResidual EhatConvenient
    (qMinusNX x * qMinusD x) (qMinusNY x y) (qMinusD x ^ 3) = 0
  unfold projectiveResidual qMinusNX qMinusNY qMinusD
  simp only [EhatConvenient, alphaMinus, betaMinus, gammaMinus, c3, c2,
    c0, D0, rp, rm, A0, q0, curveF]
  field_simp
  ring_nf
  rw [hC]
  simp only [curveF]
  n18q_ring

end

end MazurProof.N18RouteC.Quotients
