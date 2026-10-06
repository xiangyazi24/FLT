import FLT.Assumptions.MazurProof.N25F_BinaryResidueOrder
import Mathlib.FieldTheory.Finite.Basic

/-!
# Orders of `f ^ N - f` in a discrete valuation ring

Let `R` be a DVR with fraction field `L`, and write `ord = log ∘ ordFrac R`
for the signed order on `L`.  For a fixed exponent `N ≥ 2` and `f ≠ 0`
with `f ^ N ≠ f`:

* if `f` has a pole, `ord (f ^ N - f) = N · ord f`, because the term `f ^ N`
  is strictly more polar than `f`;
* if `f` is integral, `f ^ N - f` is integral;
* if `f` is integral and every residue `x` satisfies `x ^ N = x` (for example
  `N = 8` over a residue field `F₂` or `F₈`), then `f ^ N - f` vanishes.

These are the three local inputs of the point-counting gonality argument for
the N25 curve: a function `f` with few poles makes `f ^ 8 - f` vanish at every
closed point of degree one or three where `f` is regular.
-/

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.N25F_FrobeniusDVROrder

variable {R L : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L]

private theorem ordFrac_ne_zero' {f : L} (hf : f ≠ 0) : Ring.ordFrac R f ≠ 0 :=
  ((isUnit_iff_ne_zero.mpr hf).map (Ring.ordFrac R)).ne_zero

/-- The order is insensitive to sign. -/
private theorem ordFrac_neg' (f : L) : Ring.ordFrac R (-f) = Ring.ordFrac R f := by
  have h1 : Ring.ordFrac R (-1 : L) = 1 := by
    have hne : Ring.ordFrac R (-1 : L) ≠ 0 := ordFrac_ne_zero' (neg_ne_zero.mpr one_ne_zero)
    have hsq : Ring.ordFrac R (-1 : L) ^ 2 = 1 := by
      rw [← map_pow]; simp
    have hlog : WithZero.log (Ring.ordFrac R (-1 : L)) = 0 := by
      have := congrArg WithZero.log hsq
      rw [WithZero.log_pow, WithZero.log_one, nsmul_eq_mul] at this
      push_cast at this
      omega
    rw [← WithZero.exp_log hne, hlog, WithZero.exp_zero]
  rw [neg_eq_neg_one_mul, map_mul, h1, one_mul]

/-- An element of nonnegative order is the image of an element of `R`. -/
theorem exists_eq_algebraMap_of_log_nonneg (f : L) (hf : f ≠ 0)
    (h : 0 ≤ WithZero.log (Ring.ordFrac R f)) :
    ∃ a : R, algebraMap R L a = f := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le h
  have hϖk : Ring.ordFrac R (algebraMap R L (ϖ ^ k)) = Ring.ordFrac R f := by
    rw [map_pow, map_pow, Ring.ordFrac_irreducible hϖ, ← WithZero.exp_nsmul,
      ← WithZero.exp_log (ordFrac_ne_zero' hf), hk]
    simp
  obtain ⟨u, hu⟩ := Ring.associated_of_ordFrac_eq (R := R) _ _ hϖk
  refine ⟨(u : R) * ϖ ^ k, ?_⟩
  rw [← hu, Units.smul_def, Algebra.smul_def, map_mul]

/-- A polar element is dominated by its `N`th power. -/
theorem log_ordFrac_pow_sub_self_of_neg (N : ℕ) (hN : 2 ≤ N) (f : L) (hf : f ≠ 0)
    (hneg : WithZero.log (Ring.ordFrac R f) < 0) (hne : f ^ N - f ≠ 0) :
    WithZero.log (Ring.ordFrac R (f ^ N - f)) = N * WithZero.log (Ring.ordFrac R f) := by
  have hv0 := ordFrac_ne_zero' (R := R) hf
  have hvN : Ring.ordFrac R (f ^ N) = Ring.ordFrac R f ^ N := map_pow _ _ _
  have hlogN : WithZero.log (Ring.ordFrac R (f ^ N)) = N * WithZero.log (Ring.ordFrac R f) := by
    rw [hvN, WithZero.log_pow]
    simp
  have hfN : f ^ N ≠ 0 := pow_ne_zero _ hf
  have hvfN := ordFrac_ne_zero' (R := R) hfN
  have hlt : Ring.ordFrac R (f ^ N) < Ring.ordFrac R (-f) := by
    rw [ordFrac_neg']
    rw [← WithZero.log_lt_log hvfN hv0, hlogN]
    have : (2 : ℤ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hmin := Ring.ordFrac_add (R := R) (f ^ N) (-f) (by simpa [sub_eq_add_neg] using hne)
  have hnf : -f ≠ 0 := neg_ne_zero.mpr hf
  -- the reverse inequality: f ^ N = (f ^ N - f) + f
  have hrev := Ring.ordFrac_add (R := R) (f ^ N - f) f (by simpa using hfN)
  rw [sub_add_cancel] at hrev
  rw [min_eq_left hlt.le, ← sub_eq_add_neg] at hmin
  have hvs := ordFrac_ne_zero' (R := R) hne
  have hle : Ring.ordFrac R (f ^ N - f) ≤ Ring.ordFrac R (f ^ N) := by
    by_contra hcon
    push Not at hcon
    have hlt' : Ring.ordFrac R (f ^ N) < Ring.ordFrac R f := by
      simpa [ordFrac_neg'] using hlt
    have := le_min hcon.le hlt'.le
    rcases le_total (Ring.ordFrac R (f ^ N - f)) (Ring.ordFrac R f) with h | h
    · rw [min_eq_left h] at hrev
      exact absurd (lt_of_lt_of_le hcon hrev) (lt_irrefl _)
    · rw [min_eq_right h] at hrev
      exact absurd (lt_of_lt_of_le hlt' hrev) (lt_irrefl _)
  have heq : Ring.ordFrac R (f ^ N - f) = Ring.ordFrac R (f ^ N) := le_antisymm hle hmin
  rw [heq, hlogN]

/-- An integral element has integral `f ^ N - f`. -/
theorem log_ordFrac_pow_sub_self_nonneg (N : ℕ) (f : L) (hf : f ≠ 0)
    (h : 0 ≤ WithZero.log (Ring.ordFrac R f)) (hne : f ^ N - f ≠ 0) :
    0 ≤ WithZero.log (Ring.ordFrac R (f ^ N - f)) := by
  obtain ⟨a, rfl⟩ := exists_eq_algebraMap_of_log_nonneg (R := R) f hf h
  have hs : a ^ N - a ≠ 0 := by
    intro h0; apply hne; rw [← map_pow, ← map_sub, h0, map_zero]
  rw [← map_pow, ← map_sub]
  have hv := Ring.ordFrac_ge_one_of_ne_zero (K := L) hs
  have hv0 := ordFrac_ne_zero' (R := R) hne
  rw [← map_pow, ← map_sub] at hv0
  simpa only [WithZero.log_one] using
    (WithZero.log_le_log (show (1 : WithZero (Multiplicative ℤ)) ≠ 0 from one_ne_zero) hv0).mpr hv

/-- If every residue is fixed by `x ↦ x ^ N`, an integral element `f` has
`f ^ N - f` of strictly positive order. -/
theorem log_ordFrac_pow_sub_self_pos (N : ℕ) (f : L) (hf : f ≠ 0)
    (h : 0 ≤ WithZero.log (Ring.ordFrac R f)) (hne : f ^ N - f ≠ 0)
    (hres : ∀ x : IsLocalRing.ResidueField R, x ^ N = x) :
    0 < WithZero.log (Ring.ordFrac R (f ^ N - f)) := by
  obtain ⟨a, rfl⟩ := exists_eq_algebraMap_of_log_nonneg (R := R) f hf h
  have hs : a ^ N - a ≠ 0 := by
    intro h0; apply hne; rw [← map_pow, ← map_sub, h0, map_zero]
  have hres0 : IsLocalRing.residue R (a ^ N - a) = 0 := by
    rw [map_sub, map_pow, hres, sub_self]
  have hnot : ¬ IsUnit (a ^ N - a) :=
    (IsLocalRing.mem_maximalIdeal _).mp ((IsLocalRing.residue_eq_zero_iff _).mp hres0)
  have hsL : algebraMap R L (a ^ N - a) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R L)).mpr hs
  have hv0 := ordFrac_ne_zero' (R := R) hsL
  have hv1 : Ring.ordFrac R (algebraMap R L (a ^ N - a)) ≠ 1 := by
    intro h1
    exact hnot (Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing.mpr h1)
  have hpos : 1 < Ring.ordFrac R (algebraMap R L (a ^ N - a)) :=
    lt_of_le_of_ne (Ring.ordFrac_ge_one_of_ne_zero hs) (Ne.symm hv1)
  rw [← map_pow, ← map_sub]
  simpa only [WithZero.log_one] using
    (WithZero.log_lt_log (show (1 : WithZero (Multiplicative ℤ)) ≠ 0 from one_ne_zero) hv0).mpr hpos

/-- In a finite field of `2 ^ d` elements with `d ∣ 3`, every element is a
root of `X ^ 8 - X`. -/
theorem pow_eight_eq_self_of_card {F : Type*} [Field F] [Fintype F] (d : ℕ)
    (hcard : Fintype.card F = 2 ^ d) (hd : d ∣ 3) (x : F) : x ^ 8 = x := by
  have hd' : d = 1 ∨ d = 3 := by
    have := (Nat.dvd_prime Nat.prime_three).mp hd
    omega
  have hq := FiniteField.pow_card x
  rcases hd' with rfl | rfl
  · rw [hcard] at hq
    norm_num at hq
    calc x ^ 8 = ((x ^ 2) ^ 2) ^ 2 := by ring
      _ = x := by rw [hq, hq, hq]
  · rw [hcard] at hq
    norm_num at hq
    exact hq

end MazurProof.N25F_FrobeniusDVROrder
