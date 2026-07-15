import Mathlib
import FLT.Assumptions.MazurProof.DescentBridgeN16Defs

/-!
# Kubert bridge: Z/2Z x Z/16Z torsion -> point on w^2 = u^3 - u^2 - u

This file isolates the N=16 Tate/Kubert input from the elementary algebra.
The polynomial identities below are the tractable rational algebra in Tate
normal form; the remaining geometric inputs are left as named `sorry` theorems.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.KubertBridgeN16

noncomputable section

/-! ## Tate-normal-form algebra for the N=16 layer -/

def tateTwoTorsionCubic16 (b c X : ℚ) : ℚ :=
  4 * X ^ 3 + ((1 - c) ^ 2 - 4 * b) * X ^ 2 + 2 * b * (c - 1) * X + b ^ 2

def tateM16 (b c : ℚ) : ℚ :=
  2 * b ^ 2 - b * c ^ 2 - 3 * b * c + c ^ 2

def tateN16 (b c : ℚ) : ℚ :=
  b ^ 2 - b * c - c ^ 3

def tateL16 (b c : ℚ) : ℚ :=
  b ^ 3 - 3 * b ^ 2 * c + b * c ^ 3 + 3 * b * c ^ 2 - c ^ 5 - c ^ 4 - c ^ 3

def tateK16 (b c : ℚ) : ℚ :=
  b ^ 3 - 3 * b ^ 2 * c ^ 2 - 2 * b ^ 2 * c + b * c ^ 4 + 3 * b * c ^ 3 +
    b * c ^ 2 + c ^ 5

def tateX8 (b c : ℚ) : ℚ :=
  b * tateN16 b c * tateL16 b c / (c ^ 2 * (tateM16 b c) ^ 2)

def tateY8 (b c : ℚ) : ℚ :=
  -b * (b - c) * (tateN16 b c) ^ 2 * tateK16 b c /
    (c ^ 3 * (tateM16 b c) ^ 3)

def Phi16 (b c : ℚ) : ℚ :=
  2 * b ^ 8 - 4 * b ^ 7 * c ^ 2 - 12 * b ^ 7 * c +
    b ^ 6 * c ^ 4 + 18 * b ^ 6 * c ^ 3 + 31 * b ^ 6 * c ^ 2 -
    35 * b ^ 5 * c ^ 4 - 45 * b ^ 5 * c ^ 3 +
    40 * b ^ 4 * c ^ 5 + 40 * b ^ 4 * c ^ 4 -
    10 * b ^ 3 * c ^ 8 - 10 * b ^ 3 * c ^ 7 - 30 * b ^ 3 * c ^ 6 -
    22 * b ^ 3 * c ^ 5 +
    4 * b ^ 2 * c ^ 10 + 20 * b ^ 2 * c ^ 9 + 15 * b ^ 2 * c ^ 8 +
    14 * b ^ 2 * c ^ 7 + 7 * b ^ 2 * c ^ 6 -
    b * c ^ 12 - 3 * b * c ^ 11 - 10 * b * c ^ 10 - 6 * b * c ^ 9 -
    3 * b * c ^ 8 - b * c ^ 7 - c ^ 12

def tatePsi8 (b c : ℚ) : ℚ :=
  2 * tateY8 b c + (1 - c) * tateX8 b c - b

def tateQ16bc (b c X : ℚ) : ℚ :=
  let r := tateX8 b c
  let A := (1 - c) ^ 2 - 4 * b
  let B := 2 * b * (c - 1)
  4 * X ^ 2 + (A + 4 * r) * X + (B + A * r + 4 * r ^ 2)

def eta16bc (b c X : ℚ) : ℚ :=
  let r := tateX8 b c
  let A := (1 - c) ^ 2 - 4 * b
  8 * X + (A + 4 * r)

def discQ16bc (b c : ℚ) : ℚ :=
  let r := tateX8 b c
  let A := (1 - c) ^ 2 - 4 * b
  let B := 2 * b * (c - 1)
  let q1 := A + 4 * r
  let q0 := B + A * r + 4 * r ^ 2
  q1 ^ 2 - 16 * q0

theorem tatePsi8_identity
    (b c : ℚ)
    (hc : c ≠ 0)
    (hM : tateM16 b c ≠ 0) :
    2 * tateY8 b c + (1 - c) * tateX8 b c - b =
      -b * Phi16 b c / (c ^ 3 * (tateM16 b c) ^ 3) := by
  unfold tateY8 tateX8 Phi16 tateN16 tateL16 tateK16
  field_simp [hc, hM]
  unfold tateM16
  ring

theorem tatePsi8_eq_zero_iff_Phi16_eq_zero
    (b c : ℚ)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hM : tateM16 b c ≠ 0) :
    2 * tateY8 b c + (1 - c) * tateX8 b c - b = 0 ↔ Phi16 b c = 0 := by
  rw [tatePsi8_identity b c hc hM]
  have hden : c ^ 3 * (tateM16 b c) ^ 3 ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero 3 hc) (pow_ne_zero 3 hM)
  constructor
  · intro h
    have hnum : -b * Phi16 b c = 0 := by
      field_simp [hden] at h
      simpa using h
    exact (mul_eq_zero.mp hnum).resolve_left (neg_ne_zero.mpr hb)
  · intro h
    simp [h]

theorem tateTwoTorsionCubic16_x8_eq_tatePsi8_sq
    (b c : ℚ)
    (hc : c ≠ 0)
    (hM : tateM16 b c ≠ 0) :
    tateTwoTorsionCubic16 b c (tateX8 b c) =
      (2 * tateY8 b c + (1 - c) * tateX8 b c - b) ^ 2 := by
  unfold tateTwoTorsionCubic16 tateY8 tateX8 tateN16 tateL16 tateK16
  field_simp [hc, hM]
  unfold tateM16
  ring

theorem tateTwoTorsionCubic16_x8_eq_zero_of_Phi16
    (b c : ℚ)
    (hc : c ≠ 0)
    (hM : tateM16 b c ≠ 0)
    (hPhi : Phi16 b c = 0) :
    tateTwoTorsionCubic16 b c (tateX8 b c) = 0 := by
  rw [tateTwoTorsionCubic16_x8_eq_tatePsi8_sq b c hc hM]
  rw [tatePsi8_identity b c hc hM, hPhi]
  ring

theorem tateTwoTorsionCubic16_sub_x8_factor
    (b c X : ℚ) :
    tateTwoTorsionCubic16 b c X -
        tateTwoTorsionCubic16 b c (tateX8 b c) =
      (X - tateX8 b c) * tateQ16bc b c X := by
  unfold tateTwoTorsionCubic16 tateQ16bc
  ring

theorem tateQ16bc_eq_zero_of_two_torsion_root
    (b c xT : ℚ)
    (hc : c ≠ 0)
    (hM : tateM16 b c ≠ 0)
    (hPhi : Phi16 b c = 0)
    (hroot : tateTwoTorsionCubic16 b c xT = 0)
    (hne : xT ≠ tateX8 b c) :
    tateQ16bc b c xT = 0 := by
  have hr : tateTwoTorsionCubic16 b c (tateX8 b c) = 0 :=
    tateTwoTorsionCubic16_x8_eq_zero_of_Phi16 b c hc hM hPhi
  have hfac := tateTwoTorsionCubic16_sub_x8_factor b c xT
  rw [hroot, hr] at hfac
  have hprod : (xT - tateX8 b c) * tateQ16bc b c xT = 0 := by
    simpa using hfac.symm
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)

theorem eta16bc_sq_sub_disc
    (b c X : ℚ) :
    (eta16bc b c X) ^ 2 - discQ16bc b c =
      16 * tateQ16bc b c X := by
  unfold eta16bc discQ16bc tateQ16bc
  ring

theorem eta16bc_sq_eq_disc_of_Q16bc_root
    (b c xT : ℚ)
    (hQ : tateQ16bc b c xT = 0) :
    (eta16bc b c xT) ^ 2 = discQ16bc b c := by
  have h := eta16bc_sq_sub_disc b c xT
  rw [hQ, mul_zero] at h
  nlinarith

/-! ## Discriminant factorization: integralizing the residual square condition

`discQ16bc b c` is a rational function whose numerator, after clearing the
square denominator `(c ^ 2 * tateM16 b c ^ 2) ^ 2`, factors as the negative of
`descentG1 b c * descentG2 b c` (identity checked by `ring`).  Consequently the
residual 2-torsion square condition
`eta ^ 2 = discQ16bc b c` is equivalent to the *polynomial* square condition

  `(eta * (c ^ 2 * tateM16 b c ^ 2)) ^ 2 = -(descentG1 b c * descentG2 b c)`,

an integral entry point for the remaining descent on the order-16 modular
locus.  Any coprimality or factor-splitting property needed later must be proved
separately. -/

def descentG1 (b c : ℚ) : ℚ :=
  6 * b ^ 3 - 4 * b ^ 2 * c ^ 2 - 12 * b ^ 2 * c + b * c ^ 4 + 2 * b * c ^ 3
    + 7 * b * c ^ 2 + c ^ 4 - c ^ 3

def descentG2 (b c : ℚ) : ℚ :=
  8 * b ^ 9 - 16 * b ^ 8 * c ^ 2 - 48 * b ^ 8 * c - 28 * b ^ 7 * c ^ 4 + 72 * b ^ 7 * c ^ 3
    + 124 * b ^ 7 * c ^ 2 + 80 * b ^ 6 * c ^ 6 + 144 * b ^ 6 * c ^ 5 - 172 * b ^ 6 * c ^ 4
    - 180 * b ^ 6 * c ^ 3 - 50 * b ^ 5 * c ^ 8 - 264 * b ^ 5 * c ^ 7 - 276 * b ^ 5 * c ^ 6
    + 296 * b ^ 5 * c ^ 5 + 158 * b ^ 5 * c ^ 4 + 12 * b ^ 4 * c ^ 10 + 84 * b ^ 4 * c ^ 9
    + 372 * b ^ 4 * c ^ 8 + 292 * b ^ 4 * c ^ 7 - 360 * b ^ 4 * c ^ 6 - 80 * b ^ 4 * c ^ 5
    - b ^ 3 * c ^ 12 - 6 * b ^ 3 * c ^ 11 - 73 * b ^ 3 * c ^ 10 - 316 * b ^ 3 * c ^ 9
    - 201 * b ^ 3 * c ^ 8 + 286 * b ^ 3 * c ^ 7 + 15 * b ^ 3 * c ^ 6 + 13 * b ^ 2 * c ^ 12
    + 39 * b ^ 2 * c ^ 11 + 130 * b ^ 2 * c ^ 10 + 78 * b ^ 2 * c ^ 9 - 139 * b ^ 2 * c ^ 8
    + 7 * b ^ 2 * c ^ 7 + 13 * b * c ^ 12 - 12 * b * c ^ 10 + 36 * b * c ^ 9 - 5 * b * c ^ 8
    - c ^ 12 + 3 * c ^ 11 - 3 * c ^ 10 + c ^ 9

/-- The exact discriminant factorization (checked by `ring`): clearing the square
denominator `(c ^ 2 * tateM16 b c ^ 2) ^ 2` turns `discQ16bc` into the negated
product `-(descentG1 * descentG2)`. -/
theorem discQ16bc_mul_sq_den (b c : ℚ) (hc : c ≠ 0) (hM : tateM16 b c ≠ 0) :
    discQ16bc b c * (c ^ 2 * (tateM16 b c) ^ 2) ^ 2
      = -(descentG1 b c * descentG2 b c) := by
  unfold discQ16bc tateX8 tateN16 tateL16 descentG1 descentG2
  field_simp [hc, hM]
  unfold tateM16
  ring

/-- Integralized form of the residual 2-torsion square condition.  From
`eta ^ 2 = discQ16bc b c` (with `c ≠ 0`, `tateM16 b c ≠ 0`) one obtains a genuine
*polynomial* square identity, eliminating all denominators. -/
theorem descent_square_of_disc
    (b c eta : ℚ) (hc : c ≠ 0) (hM : tateM16 b c ≠ 0)
    (hDisc : eta ^ 2 = discQ16bc b c) :
    (eta * (c ^ 2 * (tateM16 b c) ^ 2)) ^ 2
      = -(descentG1 b c * descentG2 b c) := by
  have h := discQ16bc_mul_sq_den b c hc hM
  have hrw : (eta * (c ^ 2 * (tateM16 b c) ^ 2)) ^ 2
      = eta ^ 2 * (c ^ 2 * (tateM16 b c) ^ 2) ^ 2 := by ring
  rw [hrw, hDisc, h]

/-! ## Checked group-theoretic extraction from `ZMod 2 x ZMod 16` -/

private def zmod16ToZmod2xZmod16 : ZMod 16 →+ (ZMod 2 × ZMod 16) where
  toFun x := (0, x)
  map_zero' := by
    ext <;> simp
  map_add' := by
    intro x y
    ext <;> simp

private theorem zmod16ToZmod2xZmod16_injective :
    Function.Injective zmod16ToZmod2xZmod16 := by
  intro x y h
  exact congrArg Prod.snd h

private theorem addOrderOf_zmod2x16_zero_one :
    addOrderOf ((0, 1) : ZMod 2 × ZMod 16) = 16 := by
  have h := addOrderOf_injective
    zmod16ToZmod2xZmod16 zmod16ToZmod2xZmod16_injective (1 : ZMod 16)
  simpa [zmod16ToZmod2xZmod16, ZMod.addOrderOf_one] using h

/-- The injection supplies a rational point of additive order `16`. -/
theorem point_addOrder16_of_zmod2_zmod16_injection
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (f : (ZMod 2 × ZMod 16) →+ (E⁄ℚ).Point)
    (hf : Function.Injective f) :
    ∃ P : (E⁄ℚ).Point, addOrderOf P = 16 := by
  refine ⟨f ((0, 1) : ZMod 2 × ZMod 16), ?_⟩
  have h := addOrderOf_injective f hf ((0, 1) : ZMod 2 × ZMod 16)
  simpa [addOrderOf_zmod2x16_zero_one] using h

/-- Multiplicative-order wrapper for APIs stated through `Multiplicative.ofAdd`. -/
theorem point_order16_of_zmod2_zmod16_injection
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (f : (ZMod 2 × ZMod 16) →+ (E⁄ℚ).Point)
    (hf : Function.Injective f) :
    ∃ P : (E⁄ℚ).Point, orderOf (Multiplicative.ofAdd P) = 16 := by
  rcases point_addOrder16_of_zmod2_zmod16_injection E f hf with ⟨P, hP⟩
  exact ⟨P, by simpa using hP⟩

private def zmod2ToZmod16_eight : ZMod 2 →+ ZMod 16 where
  toFun x := if x = 0 then 0 else 8
  map_zero' := by
    simp
  map_add' := by
    intro x y
    fin_cases x <;> fin_cases y <;> decide

private theorem zmod2ToZmod16_eight_injective :
    Function.Injective zmod2ToZmod16_eight := by
  intro x y h
  fin_cases x <;> fin_cases y
  · rfl
  · exfalso
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    change
      (if (0 : ZMod 2) = 0 then (0 : ZMod 16) else 8) =
        (if (1 : ZMod 2) = 0 then (0 : ZMod 16) else 8) at h
    simp only [if_true, if_false, h10] at h
    exact (by decide : ¬ ((0 : ZMod 16) = 8)) h
  · exfalso
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    change
      (if (1 : ZMod 2) = 0 then (0 : ZMod 16) else 8) =
        (if (0 : ZMod 2) = 0 then (0 : ZMod 16) else 8) at h
    simp only [if_true, if_false, h10] at h
    exact (by decide : ¬ ((8 : ZMod 16) = 0)) h
  · rfl

private def zmod2x2ToZmod2x16 :
    (ZMod 2 × ZMod 2) →+ (ZMod 2 × ZMod 16) where
  toFun x := (x.1, zmod2ToZmod16_eight x.2)
  map_zero' := by
    ext <;> simp [zmod2ToZmod16_eight]
  map_add' := by
    intro x y
    ext
    · simp
    · exact map_add zmod2ToZmod16_eight x.2 y.2

private theorem zmod2x2ToZmod2x16_injective :
    Function.Injective zmod2x2ToZmod2x16 := by
  intro x y h
  apply Prod.ext
  · have hfst :
        (zmod2x2ToZmod2x16 x).1 = (zmod2x2ToZmod2x16 y).1 :=
      congrArg Prod.fst h
    simpa [zmod2x2ToZmod2x16] using hfst
  · have hsnd :
        (zmod2x2ToZmod2x16 x).2 = (zmod2x2ToZmod2x16 y).2 :=
      congrArg Prod.snd h
    exact zmod2ToZmod16_eight_injective (by
      simpa [zmod2x2ToZmod2x16] using hsnd)

/-- The injection contains a checked copy of full rational `2`-torsion. -/
theorem full_two_torsion_of_zmod2_zmod16_injection
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (f : (ZMod 2 × ZMod 16) →+ (E⁄ℚ).Point)
    (hf : Function.Injective f) :
    ∃ g : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point, Function.Injective g := by
  refine ⟨f.comp zmod2x2ToZmod2x16, ?_⟩
  intro x y hxy
  apply zmod2x2ToZmod2x16_injective
  apply hf
  exact hxy

/-! ## Residual Kubert/geometric inputs -/

/--
Tate/Kubert normal-form input for the `Z/2Z x Z/16Z` bridge.

Starting from a rational full-2-torsion structure and a rational point of
order `16`, one moves to Tate normal form.  The order-16 condition gives
`Phi16 b c = 0`; the extra rational 2-torsion point makes the remaining
quadratic factor have square discriminant.
-/
-- `AXIOM[N16-TATE-KUBERT]`: Kubert normal-form input for `ℤ/2ℤ × ℤ/16ℤ`.
-- Discharging requires the Tate normal form theorem + residual discriminant formula.
axiom kubert_C16_discriminant_data
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 16) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ b c eta : ℚ,
      b ≠ 0 ∧ c ≠ 0 ∧ tateM16 b c ≠ 0 ∧
        Phi16 b c = 0 ∧ eta ^ 2 = discQ16bc b c

/--
The birational map from the Tate/discriminant model

* `Phi16 b c = 0`;
* `eta^2 = discQ16bc b c`;

to the chosen elliptic obstruction model `w^2 = u^3 - u^2 - u`, with the
cuspidal/degenerate `u`-values excluded.
-/
-- `AXIOM[N16-BIRATIONAL-MAP]`: birational map from Tate/discriminant model
-- to `w² = u³ - u² - u`. A concrete rational-function computation.
axiom EN16_point_of_Phi16_and_disc
    (b c eta : ℚ)
    (hPhi : Phi16 b c = 0)
    (hDisc : eta ^ 2 = discQ16bc b c)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hM : tateM16 b c ≠ 0) :
    ∃ u w : ℚ, E_N16_AffineEquation u w ∧ ¬ E_N16_DegenerateParameter u

/-- Discharge `Z2xZ16_gives_non_degenerate_N16_point` from the N=16 Kubert inputs. -/
theorem bridge_N16 (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : (ZMod 2 × ZMod 16) →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ, E_N16_AffineEquation u w ∧ ¬ E_N16_DegenerateParameter u := by
  obtain ⟨b, c, eta, hb, hc, hM, hPhi, hDisc⟩ := kubert_C16_discriminant_data E hE
  exact EN16_point_of_Phi16_and_disc b c eta hPhi hDisc hb hc hM

end

end MazurProof.KubertBridgeN16
