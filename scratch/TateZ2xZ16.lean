import Mathlib

/-!
# Algebraic core for the `Z/2 x Z/16` Tate layer

This file records the tractable rational algebra in Tate normal form.  It
deliberately stops before the birational map from the Tate/discriminant model
to the chosen elliptic model for `X_1(16)`, since that is the remaining deep
geometric step rather than a clearing-denominators calculation.
-/

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

lemma tatePsi8_identity
    (b c : ℚ)
    (hc : c ≠ 0)
    (hM : tateM16 b c ≠ 0) :
    2 * tateY8 b c + (1 - c) * tateX8 b c - b =
      -b * Phi16 b c / (c ^ 3 * (tateM16 b c) ^ 3) := by
  unfold tateY8 tateX8 Phi16 tateN16 tateL16 tateK16
  field_simp [hc, hM]
  unfold tateM16
  ring

lemma tatePsi8_eq_zero_iff_Phi16_eq_zero
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

lemma tateTwoTorsionCubic16_x8_eq_tatePsi8_sq
    (b c : ℚ)
    (hc : c ≠ 0)
    (hM : tateM16 b c ≠ 0) :
    tateTwoTorsionCubic16 b c (tateX8 b c) =
      (2 * tateY8 b c + (1 - c) * tateX8 b c - b) ^ 2 := by
  unfold tateTwoTorsionCubic16 tateY8 tateX8 tateN16 tateL16 tateK16
  field_simp [hc, hM]
  unfold tateM16
  ring

lemma tateTwoTorsionCubic16_x8_eq_zero_of_Phi16
    (b c : ℚ)
    (hc : c ≠ 0)
    (hM : tateM16 b c ≠ 0)
    (hPhi : Phi16 b c = 0) :
    tateTwoTorsionCubic16 b c (tateX8 b c) = 0 := by
  rw [tateTwoTorsionCubic16_x8_eq_tatePsi8_sq b c hc hM]
  rw [tatePsi8_identity b c hc hM, hPhi]
  ring

lemma tateTwoTorsionCubic16_sub_x8_factor
    (b c X : ℚ) :
    tateTwoTorsionCubic16 b c X -
        tateTwoTorsionCubic16 b c (tateX8 b c) =
      (X - tateX8 b c) * tateQ16bc b c X := by
  unfold tateTwoTorsionCubic16 tateQ16bc
  ring

lemma tateQ16bc_eq_zero_of_two_torsion_root
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

lemma eta16bc_sq_sub_disc
    (b c X : ℚ) :
    (eta16bc b c X) ^ 2 - discQ16bc b c =
      16 * tateQ16bc b c X := by
  unfold eta16bc discQ16bc tateQ16bc
  ring

lemma eta16bc_sq_eq_disc_of_Q16bc_root
    (b c xT : ℚ)
    (hQ : tateQ16bc b c xT = 0) :
    (eta16bc b c xT) ^ 2 = discQ16bc b c := by
  have h := eta16bc_sq_sub_disc b c xT
  rw [hQ, mul_zero] at h
  nlinarith

/--
The remaining `N = 16` gap: construct the birational map from the
Tate/discriminant model

* `Phi16 b c = 0`;
* `eta^2 = discQ16bc b c`;

to the chosen model `w^2 = u^3 - u^2 - u` of `X_1(16)`, with the degenerate
`u`-values excluded.  This is intentionally not a `field_simp; ring` step and
is the only unresolved theorem in this file.
-/
theorem EN16_point_of_Phi16_and_disc
    (b c eta : ℚ)
    (hPhi : Phi16 b c = 0)
    (hDisc : eta ^ 2 = discQ16bc b c)
    (hb : b ≠ 0)
    (hc : c ≠ 0)
    (hM : tateM16 b c ≠ 0) :
    ∃ u w : ℚ,
      w ^ 2 = u ^ 3 - u ^ 2 - u ∧
        ¬ (u = -1 ∨ u = 0 ∨ u = 1) := by
  sorry
