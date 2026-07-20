import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Local obstruction checks for the 2-isogeny descent on X₀(49)

X₀(49) is the elliptic curve (Cremona 49a1, LMFDB 49.a4):

    E₄₉ : y² + xy = x³ - x² - 2x - 1.

Its split short Weierstrass model is

    E_s : V² = U³ + 21U² + 112U = U(U+7)(U+16),

with the 2-isogenous companion

    Ê_s : Z² = X³ - 42X² - 7X.

## φ-Selmer

Descent homogeneous space for squareclass `d`:
    C_d : d·w² = d²·u⁴ + 21·d·u²·v² + 112·v⁴.

The binary form `f(u,v) = d²u⁴ + 21du²v² + 112v⁴` treated as a quadratic in
`u², v²` has discriminant `(21d)² − 4·d²·112 = −7d² < 0` and positive leading
coefficient `d² > 0`, so `f(u,v) > 0` for all `(u,v) ≠ (0,0)`.

* **d < 0**: `d·w² ≤ 0 < f(u,v)` for every `(u,v,w) ≠ (0,0,0)`.
  This kills `d ∈ {-1, -2, -7, -14}` at the archimedean place.

* **d = 2**: no primitive 2-adic solution (mod 32).

* **d = 14**: no primitive 2-adic solution (mod 32).

Survivors: `{1, 7}`.

## φ̂-Selmer

Descent homogeneous space for squareclass `d`:
    Ĉ_d : d·w² = d²·u⁴ − 42·d·u²·v² − 7·v⁴.

All non-survivors are killed by 2-adic local conditions (mod 16):
`d ∈ {-1, 2, -2, 7, 14, -14}`.

Survivors: `{1, -7}`.

## Conclusion

Both Selmer groups have size 2 = |E[φ](ℚ)| = |Ê[φ̂](ℚ)|,
so `rank(E₄₉) = 0` and `E₄₉(ℚ) = {O, (2,-1)} ≅ ℤ/2ℤ`.
-/

namespace MazurProof.X049DescentObstruction

/-! ## Archimedean obstruction for negative `d` (φ-Selmer)

The binary quartic `d²u⁴ + 21du²v² + 112v⁴` is positive definite: its
discriminant as a quadratic in `(u², v²)` is `-7d² < 0`, with leading
coefficient `d² > 0`. The completing-the-square identity

    4d²·(d²u⁴ + 21du²v² + 112v⁴) = (2d²u² + 21dv²)² + 7d²v⁴

gives the lower bound.
-/

theorem phi_rhs_pos {d : ℤ} (hd : d ≠ 0)
    {u v : ℤ} (huv : ¬ (u = 0 ∧ v = 0)) :
    0 < d ^ 2 * u ^ 4 + 21 * d * u ^ 2 * v ^ 2 + 112 * v ^ 4 := by
  rcases em (v = 0) with rfl | hv
  · have hu : u ≠ 0 := by intro h; exact huv ⟨h, rfl⟩
    have : d ^ 2 * u ^ 4 + 21 * d * u ^ 2 * 0 ^ 2 + 112 * 0 ^ 4 = d ^ 2 * u ^ 4 := by ring
    rw [this]; positivity
  · have key : 4 * d ^ 2 * (d ^ 2 * u ^ 4 + 21 * d * u ^ 2 * v ^ 2 + 112 * v ^ 4) =
      (2 * d ^ 2 * u ^ 2 + 21 * d * v ^ 2) ^ 2 + 7 * d ^ 2 * v ^ 4 := by ring
    have hprod : 0 < (2 * d ^ 2 * u ^ 2 + 21 * d * v ^ 2) ^ 2 + 7 * d ^ 2 * v ^ 4 := by
      linarith [sq_nonneg (2 * d ^ 2 * u ^ 2 + 21 * d * v ^ 2),
                show (0 : ℤ) < 7 * d ^ 2 * v ^ 4 from by positivity]
    rw [← key] at hprod
    by_contra hle; push Not at hle
    linarith [mul_nonpos_of_nonneg_of_nonpos (show (0 : ℤ) ≤ 4 * d ^ 2 from by positivity) hle]

theorem phi_neg_d_no_solution {d : ℤ} (hd : d < 0) :
    ¬ ∃ u v w : ℤ, ¬ (u = 0 ∧ v = 0 ∧ w = 0) ∧
      d * w ^ 2 = d ^ 2 * u ^ 4 + 21 * d * u ^ 2 * v ^ 2 + 112 * v ^ 4 := by
  intro ⟨u, v, w, hnz, heq⟩
  have hd0 : d ≠ 0 := ne_of_lt hd
  by_cases huv : u = 0 ∧ v = 0
  · obtain ⟨rfl, rfl⟩ := huv
    simp at heq
    rcases heq with rfl | rfl
    · exact absurd rfl hd0
    · exact absurd ⟨rfl, rfl, rfl⟩ hnz
  · have hpos := phi_rhs_pos hd0 huv
    linarith [sq_nonneg w, mul_nonpos_of_nonpos_of_nonneg (le_of_lt hd) (sq_nonneg w)]

/-! ## 2-adic obstructions (φ-Selmer, positive `d`) -/

def PrimitiveMod2_32 (u v w : ZMod 32) : Bool :=
  decide (u.val % 2 ≠ 0 ∨ v.val % 2 ≠ 0 ∨ w.val % 2 ≠ 0)

set_option maxHeartbeats 0 in
theorem phi_d2_no_primitive_mod32 :
    ¬ ∃ u v w : ZMod 32,
      PrimitiveMod2_32 u v w = true ∧
        (2 : ZMod 32) * w ^ 2 =
          (4 : ZMod 32) * u ^ 4 +
          (42 : ZMod 32) * u ^ 2 * v ^ 2 +
          (112 : ZMod 32) * v ^ 4 := by
  native_decide

set_option maxHeartbeats 0 in
theorem phi_d14_no_primitive_mod32 :
    ¬ ∃ u v w : ZMod 32,
      PrimitiveMod2_32 u v w = true ∧
        (14 : ZMod 32) * w ^ 2 =
          (196 : ZMod 32) * u ^ 4 +
          (294 : ZMod 32) * u ^ 2 * v ^ 2 +
          (112 : ZMod 32) * v ^ 4 := by
  native_decide

/-! ## 2-adic obstructions (φ̂-Selmer)

Descent space: `d·w² = d²·u⁴ − 42·d·u²·v² − 7·v⁴` -/

def PrimitiveMod2_16 (u v w : ZMod 16) : Bool :=
  decide (u.val % 2 ≠ 0 ∨ v.val % 2 ≠ 0 ∨ w.val % 2 ≠ 0)

set_option maxHeartbeats 0 in
theorem phat_dm1_no_primitive_mod16 :
    ¬ ∃ u v w : ZMod 16,
      PrimitiveMod2_16 u v w = true ∧
        (-1 : ZMod 16) * w ^ 2 =
          (1 : ZMod 16) * u ^ 4 +
          (42 : ZMod 16) * u ^ 2 * v ^ 2 +
          (-7 : ZMod 16) * v ^ 4 := by
  native_decide

set_option maxHeartbeats 0 in
theorem phat_d2_no_primitive_mod16 :
    ¬ ∃ u v w : ZMod 16,
      PrimitiveMod2_16 u v w = true ∧
        (2 : ZMod 16) * w ^ 2 =
          (4 : ZMod 16) * u ^ 4 +
          (-84 : ZMod 16) * u ^ 2 * v ^ 2 +
          (-7 : ZMod 16) * v ^ 4 := by
  native_decide

set_option maxHeartbeats 0 in
theorem phat_dm2_no_primitive_mod16 :
    ¬ ∃ u v w : ZMod 16,
      PrimitiveMod2_16 u v w = true ∧
        (-2 : ZMod 16) * w ^ 2 =
          (4 : ZMod 16) * u ^ 4 +
          (84 : ZMod 16) * u ^ 2 * v ^ 2 +
          (-7 : ZMod 16) * v ^ 4 := by
  native_decide

set_option maxHeartbeats 0 in
theorem phat_d7_no_primitive_mod16 :
    ¬ ∃ u v w : ZMod 16,
      PrimitiveMod2_16 u v w = true ∧
        (7 : ZMod 16) * w ^ 2 =
          (49 : ZMod 16) * u ^ 4 +
          (-294 : ZMod 16) * u ^ 2 * v ^ 2 +
          (-7 : ZMod 16) * v ^ 4 := by
  native_decide

set_option maxHeartbeats 0 in
theorem phat_d14_no_primitive_mod16 :
    ¬ ∃ u v w : ZMod 16,
      PrimitiveMod2_16 u v w = true ∧
        (14 : ZMod 16) * w ^ 2 =
          (196 : ZMod 16) * u ^ 4 +
          (-588 : ZMod 16) * u ^ 2 * v ^ 2 +
          (-7 : ZMod 16) * v ^ 4 := by
  native_decide

set_option maxHeartbeats 0 in
theorem phat_dm14_no_primitive_mod16 :
    ¬ ∃ u v w : ZMod 16,
      PrimitiveMod2_16 u v w = true ∧
        (-14 : ZMod 16) * w ^ 2 =
          (196 : ZMod 16) * u ^ 4 +
          (588 : ZMod 16) * u ^ 2 * v ^ 2 +
          (-7 : ZMod 16) * v ^ 4 := by
  native_decide

end MazurProof.X049DescentObstruction
