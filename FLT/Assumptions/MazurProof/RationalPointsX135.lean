import Mathlib
import FLT.Assumptions.MazurProof.TateOriginDivision
import FLT.Assumptions.MazurProof.RationalPointsX135Descent

/-!
# Rational points on the level-35 quotient

This file records Kubert's affine model of `X₀(35)`, the quotient by the
Atkin--Lehner involution `w₅`, and the resulting conductor-35 elliptic curve.
All maps below are explicit rational functions over `ℚ`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.RationalPointsX135

noncomputable section

open Polynomial

/-! ## The fiber-product and hyperelliptic models -/

/-- The standard `X₀(5)` numerator in its Hauptmodul `a`. -/
def J5Numerator (a : ℚ) : ℚ := (a ^ 2 + 10 * a + 5) ^ 3

/-- The standard `X₀(7)` numerator in its Hauptmodul `b`. -/
def J7Numerator (b : ℚ) : ℚ :=
  (b ^ 2 + 13 * b + 49) * (b ^ 2 + 5 * b + 1) ^ 3

/-- The affine fiber product `X₀(5) ×_j X₀(7)`. -/
def X035FiberEquation (a b : ℚ) : Prop :=
  b * J5Numerator a = a * J7Numerator b

/-- Kubert's hyperelliptic polynomial for `X₀(35)`. -/
def hyperellipticF35 (x : ℚ) : ℚ :=
  x ^ 8 - 4 * x ^ 7 - 6 * x ^ 6 - 4 * x ^ 5 - 9 * x ^ 4 +
    4 * x ^ 3 - 6 * x ^ 2 + 4 * x + 1

def OnX035 (x y : ℚ) : Prop := y ^ 2 = hyperellipticF35 x

/-! ## The degree-two quotient to `35A1` -/

def quotientU (x : ℚ) : ℚ := x - 1 / x

def quotientV (x y : ℚ) : ℚ := y * (1 + 1 / x ^ 4)

def quotientW (x : ℚ) : ℚ :=
  (x ^ 2 - 6 * x - 1) / (x ^ 2 + x - 1)

def quotientZ (x y : ℚ) : ℚ :=
  7 * y / (2 * (x ^ 2 + x - 1) ^ 2) - 1 / 2

/-- The optimal conductor-35 quotient, Cremona label `35a1`. -/
def E35Curve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 1
  a₃ := 1
  a₄ := 9
  a₆ := 1

def OnE35 (w z : ℚ) : Prop :=
  z ^ 2 + z = w ^ 3 + w ^ 2 + 9 * w + 1

theorem E35Curve_delta : E35Curve.Δ = (-42875 : ℚ) := by
  norm_num [E35Curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance E35Curve_isElliptic : E35Curve.IsElliptic where
  isUnit := by rw [E35Curve_delta]; norm_num

@[simp] theorem E35Curve_equation_iff (w z : ℚ) :
    WeierstrassCurve.Affine.Equation E35Curve w z ↔ OnE35 w z := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [E35Curve, OnE35]

private theorem quotientU_add_one_ne_zero {x : ℚ} (hx : x ≠ 0) :
    quotientU x + 1 ≠ 0 := by
  intro h
  have hquad : x ^ 2 + x - 1 = 0 := by
    unfold quotientU at h
    field_simp [hx] at h
    linarith
  have hsquare : (2 * x + 1) ^ 2 = 5 := by nlinarith
  have hnot : ¬ IsSquare (5 : ℚ) := by norm_num
  exact hnot ⟨2 * x + 1, by simpa [pow_two] using hsquare.symm⟩

private theorem quotientU_sq_add_two_ne_zero (x : ℚ) :
    quotientU x ^ 2 + 2 ≠ 0 := by
  nlinarith [sq_nonneg (quotientU x)]

private theorem quotientDenominator_ne_zero {x : ℚ} (hx : x ≠ 0) :
    x ^ 2 + x - 1 ≠ 0 := by
  intro h
  apply quotientU_add_one_ne_zero hx
  unfold quotientU
  field_simp [hx]
  linarith

/-- The literal rational-function identity for
`X₀(35) → X₀(35)/w₅ = 35a1`. -/
theorem map_to_E35 {x y : ℚ} (hx : x ≠ 0) (hxy : OnX035 x y) :
    OnE35 (quotientW x) (quotientZ x y) := by
  have hd := quotientDenominator_ne_zero hx
  unfold OnX035 hyperellipticF35 at hxy
  unfold OnE35 quotientW quotientZ
  set d : ℚ := x ^ 2 + x - 1 with hd_def
  have hd' : d ≠ 0 := by simpa [d] using hd
  field_simp [hd']
  ring_nf
  rw [hxy]
  ring

theorem quotientW_ne_one {x : ℚ} (hx : x ≠ 0) : quotientW x ≠ 1 := by
  have hd := quotientDenominator_ne_zero hx
  intro h
  unfold quotientW at h
  have h' := (div_eq_iff hd).mp h
  have : x = 0 := by linarith
  exact hx this

/-! ## A certified inverse from the Hauptmodul fiber -/

def inverseXDen (a b : ℚ) : ℚ :=
  347 * b + 384 * b ^ 2 + 133 * b ^ 3 + 19 * b ^ 4 + b ^ 5 - 136 * a -
    15 * a * b + 4 * a * b ^ 2 - 51 * a ^ 2 - 8 * a ^ 2 * b +
    a ^ 2 * b ^ 2 - 4 * a ^ 3 - a ^ 3 * b

def inverseXNum (a b : ℚ) : ℚ :=
  3 - 74 * b - 63 * b ^ 2 - 14 * b ^ 3 - b ^ 4 + 23 * a - 54 * a * b -
    63 * a * b ^ 2 - 14 * a * b ^ 3 - a * b ^ 4 + 4 * a ^ 2 +
    4 * a ^ 2 * b

def inverseB7Num (a b : ℚ) : ℚ :=
  inverseXNum a b ^ 2 - 3 * inverseXNum a b * inverseXDen a b -
    inverseXDen a b ^ 2

def inverseA7Num (a b : ℚ) : ℚ :=
  -inverseXDen a b ^ 6 - 5 * inverseXNum a b * inverseXDen a b ^ 5 +
    5 * inverseXNum a b ^ 3 * inverseXDen a b ^ 3 -
    5 * inverseXNum a b ^ 5 * inverseXDen a b + inverseXNum a b ^ 6

def inverseYNum (a b : ℚ) : ℚ :=
  2 * inverseXNum a b * b * inverseXDen a b ^ 5 - inverseA7Num a b

def hyperellipticHomogeneous (a b : ℚ) : ℚ :=
  inverseXNum a b ^ 8 - 4 * inverseXNum a b ^ 7 * inverseXDen a b -
    6 * inverseXNum a b ^ 6 * inverseXDen a b ^ 2 -
    4 * inverseXNum a b ^ 5 * inverseXDen a b ^ 3 -
    9 * inverseXNum a b ^ 4 * inverseXDen a b ^ 4 +
    4 * inverseXNum a b ^ 3 * inverseXDen a b ^ 5 -
    6 * inverseXNum a b ^ 2 * inverseXDen a b ^ 6 +
    4 * inverseXNum a b * inverseXDen a b ^ 7 + inverseXDen a b ^ 8

private def inverseCertificate (a b : ℚ) : ℚ :=
  ((33048 + a * (1279233 + a * (20121237 + a * (163084770 + a * (708120690 + a * (1534001333 + a * (1366888193 +
  a * (639169912 + a * (175810800 + a * (29606400 + a * (3010304 + a * (169984 + a * 4096)))))))))))) + b *
  (((-4035825) + a * ((-126892224) + a * ((-1539142371) + a * ((-8783732490) + a * ((-7579289140) + a *
  ((-1626022212) + a * (810151009 + a * (596244846 + a * (172498840 + a * (29263040 + a * (3161088 + a * (206336
  + a * 6144)))))))))))) + b * ((192680154 + a * (4635032247 + a * (38908280673 + a * ((-26560285045) + a *
  ((-36823447840) + a * ((-9698738810) + a * (712679744 + a * (775786236 + a * (162714175 + a * (18248400 + a *
  (1364640 + a * (88320 + a * 3840)))))))))))) + b * (((-4425749082) + a * ((-72066649479) + a * (257709805474 +
  a * (34466009110 + a * ((-86611519905) + a * ((-32752544549) + a * ((-2389478406) + a * (658593946 + a *
  (151940370 + a * (13768420 + a * (559312 + a * (9920 + a * 1280)))))))))))) + b * ((46411120203 + a *
  ((-615560262767) + a * (609224161182 + a * (310952898075 + a * ((-72102505065) + a * ((-48969617588) + a *
  ((-6519840541) + a * (72210211 + a * (82461850 + a * (7784765 + a * (345151 + a * ((-4040) + a *
  240)))))))))))) + b * ((484883113735 + a * ((-1930254912702) + a * (615383188597 + a * (627526261980 + a *
  (22133736000 + a * ((-37637675359) + a * ((-6523213885) + a * ((-265699725) + a * (24416445 + a * (2369020 + a
  * (160365 + a * ((-1554) + a * 24)))))))))))) + b * ((1738772919632 + a * ((-3350100852216) + a * (75559051656
  + a * (663717442400 + a * (92506283615 + a * ((-15832506736) + a * ((-3622825619) + a * ((-230751651) + a *
  (4154605 + a * (281285 + a * (44252 + a * ((-206) + a * 1)))))))))))) + b * ((3507146002154 + a *
  ((-3705133472166) + a * ((-491273623644) + a * (437241300800 + a * (88670291575 + a * ((-2981755159) + a *
  ((-1237709057) + a * ((-104677048) + a * (583070 + a * ((-35585) + a * (7265 + a * (-10)))))))))))) + b *
  ((4627199025039 + a * ((-2810292565030) + a * ((-620970090710) + a * (191967735860 + a * (50488411355 + a *
  (419708404 + a * ((-256062543) + a * ((-31342577) + a * (137715 + a * ((-16885) + a * 708)))))))))) + b *
  ((4304989682835 + a * ((-1528922544326) + a * ((-419355614539) + a * (56833690110 + a * (20022558825 + a *
  (437376174 + a * ((-24415961) + a * ((-6590759) + a * (32210 + a * ((-2435) + a * 39)))))))))) + b *
  ((2954814201672 + a * ((-614290420987) + a * ((-189267892703) + a * (10554672830 + a * (5897714785 + a *
  (139071272 + a * (2236827 + a * ((-982157) + a * (4460 + a * ((-170) + a * 1)))))))))) + b * ((1541476171660 +
  a * ((-185708581373) + a * ((-61403299752) + a * (720185565 + a * (1329109705 + a * (27020077 + a * (1116377 +
  a * ((-101572) + a * (325 + a * (-5)))))))))) + b * ((623851276046 + a * ((-42686026144) + a * ((-14786596691)
  + a * ((-229842800) + a * (231390995 + a * (3618807 + a * (175648 + a * ((-6923) + a * 10)))))))) + b *
  ((198614490857 + a * ((-7481162621) + a * ((-2677908579) + a * ((-91055290) + a * (30957145 + a * (351386 + a
  * (15204 + a * (-279)))))))) + b * ((50178738727 + a * ((-994520920) + a * ((-364771985) + a * ((-17313985) +
  a * (3123235 + a * (25502 + a * (725 + a * (-5)))))))) + b * ((10101745512 + a * ((-98765699) + a *
  ((-36915126) + a * ((-2137915) + a * (229440 + a * (1386 + a * 15)))))) + b * ((1619728823 + a * ((-7112229) +
  a * ((-2698521) + a * ((-179235) + a * (11550 + a * 52))))) + b * ((205711822 + a * ((-351495) + a *
  ((-134990) + a * ((-9930) + a * (355 + a * 1))))) + b * ((20451653 + a * ((-10686) + a * ((-4144) + a *
  ((-330) + a * 5)))) + b * ((1559412 + a * ((-151) + a * ((-59) + a * (-5)))) + b * (88140 + b * (3483 + b *
  (86 + b * 1)))))))))))))))))))))))

private def fiberFactorTwo (b : ℚ) : ℚ := b ^ 2 + 5 * b + 1

private def fiberFactorFour (b : ℚ) : ℚ :=
  b ^ 4 + 14 * b ^ 3 + 63 * b ^ 2 + 70 * b - 7

private def fiberFactorFive (b : ℚ) : ℚ :=
  b ^ 5 + 26 * b ^ 4 + 267 * b ^ 3 + 1338 * b ^ 2 + 3233 * b + 3072

private theorem fiberFactorTwo_ne_zero (b : ℚ) : fiberFactorTwo b ≠ 0 := by
  intro h
  have hsquare : (2 * b + 5) ^ 2 = 21 := by
    unfold fiberFactorTwo at h
    nlinarith
  have hnot : ¬ IsSquare (21 : ℚ) := by norm_num
  exact hnot ⟨2 * b + 5, by simpa [pow_two] using hsquare.symm⟩

private theorem int_dvd_seven_cases {z : ℤ} (hz : z ∣ (7 : ℤ)) :
    z = 1 ∨ z = -1 ∨ z = 7 ∨ z = -7 := by
  have habs : z.natAbs ∣ 7 := (Int.natAbs_dvd_natAbs).mpr hz
  have habsCases : z.natAbs = 1 ∨ z.natAbs = 7 :=
    (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp habs
  rcases habsCases with h1 | h7
  · rcases Int.natAbs_eq_iff.mp h1 with hz | hz
    · exact Or.inl hz
    · exact Or.inr (Or.inl hz)
  · rcases Int.natAbs_eq_iff.mp h7 with hz | hz
    · exact Or.inr (Or.inr (Or.inl hz))
    · exact Or.inr (Or.inr (Or.inr hz))

private theorem fiberFactorFour_ne_zero (b : ℚ) : fiberFactorFour b ≠ 0 := by
  intro h
  let p : ℤ[X] := X ^ 4 + C 14 * X ^ 3 + C 63 * X ^ 2 + C 70 * X - C 7
  have hpmonic : p.Monic := by
    dsimp [p]
    monicity!
  have hroot : aeval b p = 0 := by
    simp [p, aeval_def]
    unfold fiberFactorFour at h
    norm_cast
  obtain ⟨z, hb, hzdiv⟩ :=
    exists_integer_of_is_root_of_monic (A := ℤ) (K := ℚ) hpmonic hroot
  have hz7 : z ∣ (7 : ℤ) := by
    simpa [p] using hzdiv
  rcases int_dvd_seven_cases hz7 with rfl | rfl | rfl | rfl <;>
    rw [hb] at h <;> norm_num [fiberFactorFour] at h

private theorem fiberFactorFive_ne_zero (b : ℚ) : fiberFactorFive b ≠ 0 := by
  intro h
  let p : ℤ[X] :=
    X ^ 5 + C 26 * X ^ 4 + C 267 * X ^ 3 + C 1338 * X ^ 2 +
      C 3233 * X + C 3072
  have hpmonic : p.Monic := by
    dsimp [p]
    monicity!
  have hroot : aeval b p = 0 := by
    simp [p, aeval_def]
    unfold fiberFactorFive at h
    norm_cast
  obtain ⟨z, hb, _hzdiv⟩ :=
    exists_integer_of_is_root_of_monic (A := ℤ) (K := ℚ) hpmonic hroot
  rw [hb] at h
  unfold fiberFactorFive at h
  have hz : z ^ 5 + 26 * z ^ 4 + 267 * z ^ 3 + 1338 * z ^ 2 +
      3233 * z + 3072 = 0 := by
    have hzcast : ((z ^ 5 + 26 * z ^ 4 + 267 * z ^ 3 + 1338 * z ^ 2 +
        3233 * z + 3072 : ℤ) : ℚ) = 0 := by
      push_cast
      exact h
    exact_mod_cast hzcast
  have hzmod : (z : ZMod 7) ^ 5 + 26 * (z : ZMod 7) ^ 4 +
      267 * (z : ZMod 7) ^ 3 + 1338 * (z : ZMod 7) ^ 2 +
      3233 * (z : ZMod 7) + 3072 = 0 := by
    have hz' := congrArg (fun n : ℤ => (n : ZMod 7)) hz
    push_cast at hz'
    exact hz'
  exact (by decide : ∀ t : ZMod 7,
    t ^ 5 + 26 * t ^ 4 + 267 * t ^ 3 + 1338 * t ^ 2 +
      3233 * t + 3072 ≠ 0) (z : ZMod 7) hzmod

private def inverseDenBezoutFiber (a b : ℚ) : ℚ :=
  (((-6823936) + a * ((-2558976) + a * (-200704))) + b * (((-16179800) + a * ((-4250593) + a * (-311916))) + b *
  (((-16869850) + a * ((-3164821) + a * (-212807))) + b * (((-10242635) + a * ((-1390468) + a * (-84107))) + b *
  (((-4022705) + a * ((-397759) + a * (-21508))) + b * (((-1069876) + a * ((-76100) + a * (-3735))) + b *
  (((-195367) + a * ((-9451) + a * (-436))) + b * (((-24212) + a * ((-687) + a * (-31))) + b * (((-1953) + a *
  ((-22) + a * (-1))) + b * ((-93) + b * (-2)))))))))))

private def inverseDenBezoutDen (a b : ℚ) : ℚ :=
  (2458624 + b * ((3105963 + a * ((-79027200) + a * ((-65228800) + a * ((-15805440) + a * ((-1505280) + a *
  (-50176)))))) + b * ((1634709 + a * ((-269473373) + a * ((-125386268) + a * ((-24452025) + a * ((-2091050) + a
  * (-65435)))))) + b * ((491215 + a * ((-384215042) + a * ((-111718295) + a * ((-17071150) + a * ((-1276421) +
  a * (-36843)))))) + b * ((2736845 + a * ((-313697015) + a * ((-60456951) + a * ((-7085762) + a * ((-451333) +
  a * (-11816)))))) + b * ((11466471 + a * ((-166708511) + a * ((-21935030) + a * ((-1929598) + a * ((-102602) +
  a * (-2423)))))) + b * ((18487238 + a * ((-61600100) + a * ((-5585720) + a * ((-353917) + a * ((-15313) + a *
  (-328)))))) + b * ((16047959 + a * ((-16387752) + a * ((-1024899) + a * ((-42902) + a * ((-1410) + a *
  (-27)))))) + b * ((8642167 + a * ((-3180742) + a * ((-138029) + a * ((-3268) + a * ((-67) + a * (-1)))))) + b
  * ((3090520 + a * ((-447616) + a * ((-13724) + a * ((-144) + a * (-1))))) + b * ((757849 + a * ((-44424) + a *
  ((-978) + a * (-3)))) + b * ((128501 + a * ((-2935) + a * (-45))) + b * ((14860 + a * ((-115) + a * (-1))) + b
  * ((1122 + a * (-2)) + b * (50 + b * 1)))))))))))))))

private def inverseNumBezoutFiber (a b : ℚ) : ℚ :=
  ((23552 + a * 4096) + b * (((-107059) + a * (-8324)) + b * (((-2631) + a * (-39664)) + b * ((490475 + a *
  (-46340)) + b * ((718402 + a * (-25620)) + b * ((488297 + a * (-7700)) + b * ((192939 + a * (-1284)) + b *
  ((47677 + a * (-112)) + b * ((7506 + a * (-4)) + b * (735 + b * (41 + b * 1)))))))))))

private def inverseNumBezoutNum (a b : ℚ) : ℚ :=
  (50176 + b * ((58267 + a * ((-1478544) + a * ((-1312576) + a * ((-321792) + a * ((-30720) + a * (-1024)))))) +
  b * (((-315074) + a * ((-33471) + a * (2657942 + a * (836894 + a * (88237 + a * 3105))))) + b * (((-13651965)
  + a * (2558427 + a * (6631538 + a * (1919914 + a * (196527 + a * 6811))))) + b * (((-58725555) + a * (2162790
  + a * (4777220 + a * (1359092 + a * (138222 + a * 4774))))) + b * (((-101447146) + a * (759375 + a * (1648682
  + a * (466018 + a * (47283 + a * 1631))))) + b * (((-96844908) + a * (128358 + a * (298052 + a * (84084 + a *
  (8526 + a * 294))))) + b * (((-58457974) + a * (9563 + a * (27378 + a * (7722 + a * (783 + a * 27))))) + b *
  (((-23885992) + a * (97 + a * (1014 + a * (286 + a * (29 + a * 1))))) + b * (((-6845465) + a * (-16)) + b *
  ((-1396874) + b * ((-202601) + b * ((-20465) + b * ((-1372) + b * ((-55) + b * (-1))))))))))))))))

set_option maxHeartbeats 0 in
private theorem inverseDenBezoutIdentity (a b : ℚ) :
    inverseDenBezoutFiber a b *
          (b * J5Numerator a - a * J7Numerator b) +
        inverseDenBezoutDen a b * inverseXDen a b =
      b * fiberFactorTwo b ^ 3 * fiberFactorFour b ^ 2 * fiberFactorFive b := by
  unfold inverseDenBezoutFiber inverseDenBezoutDen inverseXDen
    J5Numerator J7Numerator fiberFactorTwo fiberFactorFour fiberFactorFive
  ring

set_option maxHeartbeats 0 in
private theorem inverseNumBezoutIdentity (a b : ℚ) :
    inverseNumBezoutFiber a b *
          (b * J5Numerator a - a * J7Numerator b) +
        inverseNumBezoutNum a b * inverseXNum a b =
      fiberFactorTwo b ^ 3 * fiberFactorFour b ^ 2 * fiberFactorFive b := by
  unfold inverseNumBezoutFiber inverseNumBezoutNum inverseXNum
    J5Numerator J7Numerator fiberFactorTwo fiberFactorFour fiberFactorFive
  ring

theorem inverseXDen_ne_zero {a b : ℚ} (hb : b ≠ 0)
    (h : X035FiberEquation a b) : inverseXDen a b ≠ 0 := by
  intro hd
  have hi := inverseDenBezoutIdentity a b
  have hf : b * J5Numerator a - a * J7Numerator b = 0 :=
    sub_eq_zero.mpr h
  rw [hf, hd] at hi
  simp only [mul_zero, zero_add] at hi
  have hrhs :
      b * fiberFactorTwo b ^ 3 * fiberFactorFour b ^ 2 *
          fiberFactorFive b ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero hb (pow_ne_zero 3 (fiberFactorTwo_ne_zero b)))
        (pow_ne_zero 2 (fiberFactorFour_ne_zero b)))
      (fiberFactorFive_ne_zero b)
  exact hrhs hi.symm

theorem inverseXNum_ne_zero {a b : ℚ}
    (h : X035FiberEquation a b) : inverseXNum a b ≠ 0 := by
  intro hn
  have hi := inverseNumBezoutIdentity a b
  have hf : b * J5Numerator a - a * J7Numerator b = 0 :=
    sub_eq_zero.mpr h
  rw [hf, hn] at hi
  simp only [mul_zero, zero_add] at hi
  have hrhs :
      fiberFactorTwo b ^ 3 * fiberFactorFour b ^ 2 *
          fiberFactorFive b ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (pow_ne_zero 3 (fiberFactorTwo_ne_zero b))
        (pow_ne_zero 2 (fiberFactorFour_ne_zero b)))
      (fiberFactorFive_ne_zero b)
  exact hrhs hi.symm

private def inverseResidual (a b : ℚ) : ℚ :=
  b ^ 2 * inverseXDen a b ^ 5 * inverseXNum a b +
    b * inverseXDen a b ^ 6 +
    5 * b * inverseXDen a b ^ 5 * inverseXNum a b -
    5 * b * inverseXDen a b ^ 3 * inverseXNum a b ^ 3 +
    5 * b * inverseXDen a b * inverseXNum a b ^ 5 -
    b * inverseXNum a b ^ 6 +
    49 * inverseXDen a b * inverseXNum a b ^ 5

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem inverse_residual_zero {a b : ℚ}
    (h : X035FiberEquation a b) : inverseResidual a b = 0 := by
  unfold X035FiberEquation J5Numerator J7Numerator at h
  unfold inverseResidual inverseXNum inverseXDen
  linear_combination
    (norm := (simp only [inverseCertificate]; ring))
    (inverseCertificate a b) * h

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- The kernel-checked ideal-membership certificate for the inverse map. -/
theorem inverse_hyperelliptic_relation {a b : ℚ}
    (h : X035FiberEquation a b) :
    inverseYNum a b ^ 2 =
      inverseB7Num a b ^ 2 * hyperellipticHomogeneous a b := by
  have hr := inverse_residual_zero h
  unfold inverseYNum inverseA7Num inverseB7Num hyperellipticHomogeneous
  have hfactor :
      (2 * inverseXNum a b * b * inverseXDen a b ^ 5 -
            (-inverseXDen a b ^ 6 -
              5 * inverseXNum a b * inverseXDen a b ^ 5 +
              5 * inverseXNum a b ^ 3 * inverseXDen a b ^ 3 -
              5 * inverseXNum a b ^ 5 * inverseXDen a b +
              inverseXNum a b ^ 6)) ^ 2 -
          (inverseXNum a b ^ 2 -
              3 * inverseXNum a b * inverseXDen a b -
              inverseXDen a b ^ 2) ^ 2 *
            (inverseXNum a b ^ 8 -
              4 * inverseXNum a b ^ 7 * inverseXDen a b -
              6 * inverseXNum a b ^ 6 * inverseXDen a b ^ 2 -
              4 * inverseXNum a b ^ 5 * inverseXDen a b ^ 3 -
              9 * inverseXNum a b ^ 4 * inverseXDen a b ^ 4 +
              4 * inverseXNum a b ^ 3 * inverseXDen a b ^ 5 -
              6 * inverseXNum a b ^ 2 * inverseXDen a b ^ 6 +
              4 * inverseXNum a b * inverseXDen a b ^ 7 +
              inverseXDen a b ^ 8) =
        4 * inverseXDen a b ^ 5 * inverseXNum a b * inverseResidual a b := by
    unfold inverseResidual
    ring
  apply sub_eq_zero.mp
  rw [hfactor, hr]
  ring

def inverseX (a b : ℚ) : ℚ := inverseXNum a b / inverseXDen a b

def inverseY (a b : ℚ) : ℚ :=
  inverseYNum a b / (inverseB7Num a b * inverseXDen a b ^ 4)

private theorem inverseB7Num_ne_zero {a b : ℚ} (hb : b ≠ 0)
    (h : X035FiberEquation a b) : inverseB7Num a b ≠ 0 := by
  have hd := inverseXDen_ne_zero hb h
  intro hzero
  have hquad :
      (inverseXNum a b / inverseXDen a b) ^ 2 -
          3 * (inverseXNum a b / inverseXDen a b) - 1 = 0 := by
    unfold inverseB7Num at hzero
    field_simp [hd]
    linear_combination hzero
  have hsquare :
      (2 * (inverseXNum a b / inverseXDen a b) - 3) ^ 2 = 13 := by
    nlinarith
  have hnot : ¬ IsSquare (13 : ℚ) := by norm_num
  exact hnot ⟨2 * (inverseXNum a b / inverseXDen a b) - 3,
    by simpa [pow_two] using hsquare.symm⟩

/-- Every noncuspidal point of the Hauptmodul fiber lies on Kubert's affine
hyperelliptic model. -/
theorem fiber_to_X035 {a b : ℚ} (hb : b ≠ 0)
    (h : X035FiberEquation a b) :
    inverseX a b ≠ 0 ∧ OnX035 (inverseX a b) (inverseY a b) := by
  have hd := inverseXDen_ne_zero hb h
  have hn := inverseXNum_ne_zero h
  have hB7 := inverseB7Num_ne_zero hb h
  constructor
  · exact div_ne_zero hn hd
  · have hrel := inverse_hyperelliptic_relation h
    unfold OnX035 inverseX inverseY hyperellipticF35
    field_simp [hd, hB7]
    unfold hyperellipticHomogeneous at hrel
    rw [hrel]
    ring

/-! ## The three-isogeny pair used for the rank-zero calculation -/

def E35ShortCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 16
  a₃ := 0
  a₄ := 224
  a₆ := 784

def E35DualCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -432
  a₃ := 0
  a₄ := -108000
  a₆ := -6750000

def OnE35Short (x y : ℚ) : Prop := y ^ 2 = x ^ 3 + (4 * x + 28) ^ 2

def OnE35Dual (s t : ℚ) : Prop := t ^ 2 = s ^ 3 - 3 * (12 * s + 1500) ^ 2

theorem E35ShortCurve_delta : E35ShortCurve.Δ = (-175616000 : ℚ) := by
  norm_num [E35ShortCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem E35DualCurve_delta : E35DualCurve.Δ = (-29760696000000000 : ℚ) := by
  norm_num [E35DualCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance E35ShortCurve_isElliptic : E35ShortCurve.IsElliptic where
  isUnit := by rw [E35ShortCurve_delta]; norm_num

instance E35DualCurve_isElliptic : E35DualCurve.IsElliptic where
  isUnit := by rw [E35DualCurve_delta]; norm_num

@[simp] theorem E35ShortCurve_equation_iff (x y : ℚ) :
    WeierstrassCurve.Affine.Equation E35ShortCurve x y ↔ OnE35Short x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [E35ShortCurve, OnE35Short]
  ring_nf

@[simp] theorem E35DualCurve_equation_iff (s t : ℚ) :
    WeierstrassCurve.Affine.Equation E35DualCurve s t ↔ OnE35Dual s t := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [E35DualCurve, OnE35Dual]
  ring_nf

abbrev E35ShortPoint := WeierstrassCurve.Affine.Point E35ShortCurve
abbrev E35DualPoint := WeierstrassCurve.Affine.Point E35DualCurve

def threeIsogenyX (x : ℚ) : ℚ :=
  (9 * x ^ 3 + 192 * x ^ 2 + 4032 * x + 28224) / x ^ 2

def threeIsogenyY (x y : ℚ) : ℚ :=
  (27 * x ^ 3 * y - 12096 * x * y - 169344 * y) / x ^ 3

def dualThreeIsogenyX (s : ℚ) : ℚ :=
  (s ^ 3 - 576 * s ^ 2 - 216000 * s - 27000000) / (81 * s ^ 2)

def dualThreeIsogenyY (s t : ℚ) : ℚ :=
  (s ^ 3 * t + 216000 * s * t + 54000000 * t) / (729 * s ^ 3)

theorem threeIsogeny_on_curve {x y : ℚ} (hx : x ≠ 0)
    (h : OnE35Short x y) :
    OnE35Dual (threeIsogenyX x) (threeIsogenyY x y) := by
  unfold OnE35Short at h
  unfold OnE35Dual threeIsogenyX threeIsogenyY
  field_simp [hx]
  simp_rw [h]
  ring

theorem dualThreeIsogeny_on_curve {s t : ℚ} (hs : s ≠ 0)
    (h : OnE35Dual s t) :
    OnE35Short (dualThreeIsogenyX s) (dualThreeIsogenyY s t) := by
  unfold OnE35Dual at h
  unfold OnE35Short dualThreeIsogenyX dualThreeIsogenyY
  field_simp [hs]
  simp_rw [h]
  ring

private theorem dual_x_ne_zero_of_on_curve {s t : ℚ}
    (h : OnE35Dual s t) : s ≠ 0 := by
  intro hs
  rw [hs] at h
  norm_num [OnE35Dual] at h
  nlinarith [sq_nonneg t]

private theorem shortCubic_ne_zero (x : ℚ) :
    x ^ 3 + 16 * x ^ 2 + 224 * x + 784 ≠ 0 := by
  intro h
  let p : ℤ[X] := X ^ 3 + C 16 * X ^ 2 + C 224 * X + C 784
  have hpmonic : p.Monic := by
    dsimp [p]
    monicity!
  have hroot : aeval x p = 0 := by
    simp [p, aeval_def]
    norm_cast
  obtain ⟨z, hx, _hzdiv⟩ :=
    exists_integer_of_is_root_of_monic (A := ℤ) (K := ℚ) hpmonic hroot
  rw [hx] at h
  have hz : z ^ 3 + 16 * z ^ 2 + 224 * z + 784 = 0 := by
    have hzcast : ((z ^ 3 + 16 * z ^ 2 + 224 * z + 784 : ℤ) : ℚ) = 0 := by
      push_cast
      exact h
    exact_mod_cast hzcast
  have hzmod : (z : ZMod 3) ^ 3 + 16 * (z : ZMod 3) ^ 2 +
      224 * (z : ZMod 3) + 784 = 0 := by
    have hz' := congrArg (fun n : ℤ => (n : ZMod 3)) hz
    push_cast at hz'
    exact hz'
  exact (by decide : ∀ u : ZMod 3,
    u ^ 3 + 16 * u ^ 2 + 224 * u + 784 ≠ 0) (z : ZMod 3) hzmod

private theorem short_y_ne_zero {x y : ℚ} (h : OnE35Short x y) : y ≠ 0 := by
  intro hy
  apply shortCubic_ne_zero x
  unfold OnE35Short at h
  rw [hy] at h
  norm_num at h
  linear_combination -h

private theorem short_three_nsmul_of_x_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular E35ShortCurve x y)
    (hx : x = 0) :
    (3 : ℕ) •
        (WeierstrassCurve.Affine.Point.some x y h : E35ShortPoint) = 0 := by
  apply (TateOriginDivision.nsmul_eq_zero_iff_PsiSq_eval E35ShortCurve h).mpr
  rw [E35ShortCurve.ΨSq_ofNat 3]
  simp [show ¬ Even (3 : ℕ) by decide,
    WeierstrassCurve.preΨ'_three, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, E35ShortCurve, hx]
  norm_num

private theorem short_three_x_factor_ne_zero {x y : ℚ} (hx : x ≠ 0)
    (h : OnE35Short x y) :
    (3 * x + 28) * (x ^ 2 + 12 * x + 336) ≠ 0 := by
  have hquad : x ^ 2 + 12 * x + 336 ≠ 0 := by
    nlinarith [sq_nonneg (x + 6)]
  have hlin : 3 * x + 28 ≠ 0 := by
    intro hlin
    have hxval : x = -28 / 3 := by linarith
    rw [hxval] at h
    norm_num [OnE35Short] at h
    nlinarith [sq_nonneg y]
  exact mul_ne_zero hlin hquad

private theorem threeIsogenyX_ne_zero {x y : ℚ} (hx : x ≠ 0)
    (h : OnE35Short x y) : threeIsogenyX x ≠ 0 := by
  have hfac := short_three_x_factor_ne_zero hx h
  unfold threeIsogenyX
  apply div_ne_zero
  · have hid :
        9 * x ^ 3 + 192 * x ^ 2 + 4032 * x + 28224 =
          3 * (3 * x + 28) * (x ^ 2 + 12 * x + 336) := by ring
    rw [hid]
    simpa [mul_assoc] using
      mul_ne_zero (show (3 : ℚ) ≠ 0 by norm_num) hfac
  · exact pow_ne_zero 2 hx

noncomputable def threeIsogenyPoint : E35ShortPoint → E35DualPoint
  | .zero => .zero
  | .some x _y h =>
      if hx : x = 0 then .zero
      else WeierstrassCurve.Affine.Point.mk
        (E35DualCurve_equation_iff _ _ |>.2 <|
          threeIsogeny_on_curve hx (E35ShortCurve_equation_iff _ _ |>.1 h.1))

noncomputable def dualThreeIsogenyPoint : E35DualPoint → E35ShortPoint
  | .zero => .zero
  | .some s _t h =>
      if hs : s = 0 then .zero
      else WeierstrassCurve.Affine.Point.mk
        (E35ShortCurve_equation_iff _ _ |>.2 <|
          dualThreeIsogeny_on_curve hs (E35DualCurve_equation_iff _ _ |>.1 h.1))

@[simp] theorem threeIsogenyPoint_zero : threeIsogenyPoint 0 = 0 := rfl

@[simp] theorem dualThreeIsogenyPoint_zero : dualThreeIsogenyPoint 0 = 0 := rfl

theorem threeIsogenyPoint_some_of_x_ne_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular E35ShortCurve x y)
    (hx : x ≠ 0) :
    threeIsogenyPoint (.some x y h) =
      WeierstrassCurve.Affine.Point.mk
        (E35DualCurve_equation_iff _ _ |>.2 <|
          threeIsogeny_on_curve hx (E35ShortCurve_equation_iff _ _ |>.1 h.1)) := by
  simp [threeIsogenyPoint, hx]

theorem dualThreeIsogenyPoint_some_of_x_ne_zero {s t : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular E35DualCurve s t)
    (hs : s ≠ 0) :
    dualThreeIsogenyPoint (.some s t h) =
      WeierstrassCurve.Affine.Point.mk
        (E35ShortCurve_equation_iff _ _ |>.2 <|
          dualThreeIsogeny_on_curve hs (E35DualCurve_equation_iff _ _ |>.1 h.1)) := by
  simp [dualThreeIsogenyPoint, hs]

/-! ### The composition of the two three-isogenies -/

@[simp] theorem E35ShortCurve_negY (x y : ℚ) :
    WeierstrassCurve.Affine.negY E35ShortCurve x y = -y := by
  simp [WeierstrassCurve.Affine.negY, E35ShortCurve]

private def shortTangent (x y : ℚ) : ℚ :=
  (3 * x ^ 2 + 32 * x + 224) / (2 * y)

private def shortDoubleX (x y : ℚ) : ℚ :=
  shortTangent x y ^ 2 - 16 - 2 * x

private def shortDoubleY (x y : ℚ) : ℚ :=
  -(shortTangent x y * (shortDoubleX x y - x) + y)

private def shortTripleSlope (x y : ℚ) : ℚ :=
  (shortDoubleY x y - y) / (shortDoubleX x y - x)

private def shortTripleX (x y : ℚ) : ℚ :=
  shortTripleSlope x y ^ 2 - 16 - shortDoubleX x y - x

private def shortTripleY (x y : ℚ) : ℚ :=
  -(shortTripleSlope x y * (shortTripleX x y - shortDoubleX x y) +
      shortDoubleY x y)

private theorem E35ShortCurve_slope_self {x y : ℚ} (hy : y ≠ 0) :
    WeierstrassCurve.Affine.slope E35ShortCurve x x y y = shortTangent x y := by
  have hneg : y ≠ WeierstrassCurve.Affine.negY E35ShortCurve x y := by
    rw [E35ShortCurve_negY]
    intro h
    apply hy
    linarith
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
  simp [E35ShortCurve, shortTangent, WeierstrassCurve.Affine.negY]
  ring

private theorem E35ShortCurve_addX_tangent (x y : ℚ) :
    WeierstrassCurve.Affine.addX E35ShortCurve x x (shortTangent x y) =
      shortDoubleX x y := by
  simp [E35ShortCurve, shortDoubleX]
  ring

private theorem E35ShortCurve_addY_tangent (x y : ℚ) :
    WeierstrassCurve.Affine.addY E35ShortCurve x x y (shortTangent x y) =
      shortDoubleY x y := by
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX
    E35ShortCurve shortDoubleY shortDoubleX
  ring

private theorem E35ShortCurve_slope_double {x y : ℚ}
    (hxx : shortDoubleX x y ≠ x) :
    WeierstrassCurve.Affine.slope E35ShortCurve
        (shortDoubleX x y) x (shortDoubleY x y) y =
      shortTripleSlope x y := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hxx]
  rfl

private theorem E35ShortCurve_addX_double (x y : ℚ) :
    WeierstrassCurve.Affine.addX E35ShortCurve
        (shortDoubleX x y) x (shortTripleSlope x y) =
      shortTripleX x y := by
  simp [E35ShortCurve, shortTripleX]

private theorem E35ShortCurve_addY_double (x y : ℚ) :
    WeierstrassCurve.Affine.addY E35ShortCurve
        (shortDoubleX x y) x (shortDoubleY x y) (shortTripleSlope x y) =
      shortTripleY x y := by
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX
    E35ShortCurve shortTripleY shortTripleX
  ring

private theorem shortDoubleX_sub_identity {x y : ℚ} (hy : y ≠ 0)
    (h : OnE35Short x y) :
    4 * y ^ 2 * (shortDoubleX x y - x) =
      -x * (3 * x + 28) * (x ^ 2 + 12 * x + 336) := by
  unfold shortDoubleX shortTangent
  unfold OnE35Short at h
  field_simp [hy]
  rw [h]
  ring

private theorem shortDoubleX_ne_self {x y : ℚ} (hx : x ≠ 0)
    (h : OnE35Short x y) : shortDoubleX x y ≠ x := by
  have hy := short_y_ne_zero h
  have hid := shortDoubleX_sub_identity hy h
  have hfac := short_three_x_factor_ne_zero hx h
  intro heq
  rw [heq, sub_self, mul_zero] at hid
  have hnonzero : -x * ((3 * x + 28) * (x ^ 2 + 12 * x + 336)) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hx) hfac
  apply hnonzero
  simpa [mul_assoc] using hid.symm

private theorem dual_three_comp_x {x y : ℚ} (hx : x ≠ 0)
    (h : OnE35Short x y) :
    dualThreeIsogenyX (threeIsogenyX x) = shortTripleX x y := by
  have hy := short_y_ne_zero h
  have hxx := shortDoubleX_ne_self hx h
  have hphi := threeIsogenyX_ne_zero hx h
  unfold dualThreeIsogenyX shortTripleX shortTripleSlope
  field_simp [hphi, hxx]
  unfold threeIsogenyX shortDoubleY shortDoubleX shortTangent
  unfold OnE35Short at h
  field_simp [hx, hy]
  have hy4 : y ^ 4 = (x ^ 3 + (4 * x + 28) ^ 2) ^ 2 := by
    calc
      y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = _ := by rw [h]
  have hy6 : y ^ 6 = (x ^ 3 + (4 * x + 28) ^ 2) ^ 3 := by
    calc
      y ^ 6 = (y ^ 2) ^ 3 := by ring
      _ = _ := by rw [h]
  have hy8 : y ^ 8 = (x ^ 3 + (4 * x + 28) ^ 2) ^ 4 := by
    calc
      y ^ 8 = (y ^ 2) ^ 4 := by ring
      _ = _ := by rw [h]
  ring_nf
  rw [h, hy4, hy6, hy8]
  ring

private theorem dual_three_comp_y {x y : ℚ} (hx : x ≠ 0)
    (h : OnE35Short x y) :
    dualThreeIsogenyY (threeIsogenyX x) (threeIsogenyY x y) =
      shortTripleY x y := by
  have hy := short_y_ne_zero h
  have hxx := shortDoubleX_ne_self hx h
  have hphi := threeIsogenyX_ne_zero hx h
  unfold dualThreeIsogenyY shortTripleY shortTripleX shortTripleSlope
  field_simp [hphi, hxx]
  unfold threeIsogenyX threeIsogenyY shortDoubleY shortDoubleX shortTangent
  unfold OnE35Short at h
  field_simp [hx, hy]
  have hy4 : y ^ 4 = (x ^ 3 + (4 * x + 28) ^ 2) ^ 2 := by
    calc
      y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = _ := by rw [h]
  have hy6 : y ^ 6 = (x ^ 3 + (4 * x + 28) ^ 2) ^ 3 := by
    calc
      y ^ 6 = (y ^ 2) ^ 3 := by ring
      _ = _ := by rw [h]
  have hy8 : y ^ 8 = (x ^ 3 + (4 * x + 28) ^ 2) ^ 4 := by
    calc
      y ^ 8 = (y ^ 2) ^ 4 := by ring
      _ = _ := by rw [h]
  have hy12 : y ^ 12 = (x ^ 3 + (4 * x + 28) ^ 2) ^ 6 := by
    calc
      y ^ 12 = (y ^ 2) ^ 6 := by ring
      _ = _ := by rw [h]
  have hy10 : y ^ 10 = (x ^ 3 + (4 * x + 28) ^ 2) ^ 5 := by
    calc
      y ^ 10 = (y ^ 2) ^ 5 := by ring
      _ = _ := by rw [h]
  ring_nf
  rw [hy4, hy6, hy8, hy10, hy12]
  ring

set_option maxHeartbeats 0 in
/-- The explicit dual isogeny composed with the explicit three-isogeny is
multiplication by three on the short model. -/
theorem dual_comp_threeIsogenyPoint (P : E35ShortPoint) :
    dualThreeIsogenyPoint (threeIsogenyPoint P) = 3 • P := by
  cases P with
  | zero => rfl
  | some x y h =>
      have hcurve : OnE35Short x y := (E35ShortCurve_equation_iff x y).mp h.1
      by_cases hx : x = 0
      · have hzero : threeIsogenyPoint
            (WeierstrassCurve.Affine.Point.some x y h : E35ShortPoint) =
            (0 : E35DualPoint) := by
          simp only [threeIsogenyPoint]
          rw [dif_pos hx]
          change (0 : E35DualPoint) = (0 : E35DualPoint)
          rfl
        rw [hzero, dualThreeIsogenyPoint_zero]
        exact (short_three_nsmul_of_x_zero h hx).symm
      · rw [threeIsogenyPoint_some_of_x_ne_zero h hx]
        have hphi := threeIsogenyX_ne_zero hx hcurve
        change dualThreeIsogenyPoint
            (.some (threeIsogenyX x) (threeIsogenyY x y) _) = _
        rw [dualThreeIsogenyPoint_some_of_x_ne_zero _ hphi]
        have hy := short_y_ne_zero hcurve
        have hneg : y ≠ WeierstrassCurve.Affine.negY E35ShortCurve x y := by
          rw [E35ShortCurve_negY]
          intro heq
          apply hy
          linarith
        have hxx := shortDoubleX_ne_self hx hcurve
        rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, one_nsmul,
          two_nsmul]
        rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
        rw [WeierstrassCurve.Affine.Point.add_of_X_ne (by
          rw [E35ShortCurve_slope_self hy, E35ShortCurve_addX_tangent]
          exact hxx)]
        change WeierstrassCurve.Affine.Point.some
            (dualThreeIsogenyX (threeIsogenyX x))
            (dualThreeIsogenyY (threeIsogenyX x) (threeIsogenyY x y)) _ = _
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        constructor
        · rw [E35ShortCurve_slope_self hy,
            E35ShortCurve_addX_tangent, E35ShortCurve_addY_tangent,
            E35ShortCurve_slope_double hxx, E35ShortCurve_addX_double]
          exact dual_three_comp_x hx hcurve
        · rw [E35ShortCurve_slope_self hy,
            E35ShortCurve_addX_tangent, E35ShortCurve_addY_tangent,
            E35ShortCurve_slope_double hxx,
            E35ShortCurve_addY_double]
          exact dual_three_comp_y hx hcurve

/-- A cube value of the first three-descent function constructs an explicit
preimage under the dual three-isogeny. -/
theorem exists_dualThreeIsogeny_preimage_of_alpha_cube
    {x y r : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular E35ShortCurve x y)
    (hr : r ^ 3 = y - (4 * x + 28)) (hr0 : r ≠ 0) :
    ∃ Q : E35DualPoint,
      dualThreeIsogenyPoint Q =
        WeierstrassCurve.Affine.Point.some x y h := by
  have hcurve : OnE35Short x y := (E35ShortCurve_equation_iff x y).mp h.1
  have hy : y = r ^ 3 + 4 * x + 28 := by linarith
  have hrel : x ^ 3 = r ^ 3 * (r ^ 3 + 8 * x + 56) := by
    unfold OnE35Short at hcurve
    rw [hy] at hcurve
    linear_combination -hcurve
  let d : ℚ := 3 * x - 3 * r ^ 2 - 8 * r
  have hd : d ≠ 0 := by
    intro hd
    have hx : x = r ^ 2 + 8 * r / 3 := by
      dsimp [d] at hd
      linarith
    rw [hx] at hrel
    ring_nf at hrel
    apply hr0
    have : r ^ 3 = 0 := by linarith
    exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp this
  let s : ℚ := 3000 * r / d
  let t : ℚ := 9 * s * r + 12 * s + 4500
  have hs : s ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (by norm_num) hr0) hd
  have hdual : OnE35Dual s t := by
    unfold OnE35Dual
    dsimp only [t, s]
    field_simp [hd]
    dsimp only [d]
    linear_combination 729000000 * hrel
  have hxmap : dualThreeIsogenyX s = x := by
    unfold dualThreeIsogenyX
    dsimp only [s]
    field_simp [hd, hr0]
    dsimp only [d]
    linear_combination -729000000 * hrel
  have hymap : dualThreeIsogenyY s t = y := by
    rw [hy]
    unfold dualThreeIsogenyY
    dsimp only [t, s]
    field_simp [hd, hr0]
    dsimp only [d]
    linear_combination
      19683000000000 * (-2 * r ^ 2 - 4 * r + x) * hrel
  have hdualns : WeierstrassCurve.Affine.Nonsingular E35DualCurve s t :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((E35DualCurve_equation_iff s t).mpr hdual)
  let Q : E35DualPoint := WeierstrassCurve.Affine.Point.some s t hdualns
  refine ⟨Q, ?_⟩
  rw [dualThreeIsogenyPoint_some_of_x_ne_zero hdualns hs]
  change WeierstrassCurve.Affine.Point.some
      (dualThreeIsogenyX s) (dualThreeIsogenyY s t) _ =
    WeierstrassCurve.Affine.Point.some x y h
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨hxmap, hymap⟩

end

end MazurProof.RationalPointsX135
