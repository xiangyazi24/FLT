import FLT.Assumptions.MazurProof.N13GaussianCandidateDlog

/-!
# Ramified normalization at two for the N13 candidates

The prime over two is not an auxiliary table entry.  In the intrinsic
Gaussian presentation it is simply

`π = 1 - i`,

and its square is `π² = 2(-i)`.  Hence removing an even `π`-valuation by a
rational power of `2` leaves the unit `(-i)^m`, not the identity.  Its first
jet is `ζ^m`, so the parity of the half-valuation corrects the `ζ` exponent
of the global candidate.

This is the structural compatibility missing from a bare equality in the
fake square-class quotient: an arbitrary square may have odd `π`-valuation,
and dividing its square by `2` contributes a nontrivial first jet.
-/

namespace MazurProof.N13GaussianRamifiedNormalization

noncomputable section

open N13GaussianOrderTwo
open N13GaussianLocalization
open N13GaussianCandidateDlog
open N13LocalDlogTwo

abbrev L : Type :=
  N13SexticSquareclass.SexticAlgebra

abbrev Order : Type :=
  N13GaussianOrderTwo.Order

abbrev F8 : Type :=
  N13LocalDlogTwo.F8

abbrev JetUnit : Type :=
  (DualNumber F8)ˣ

/-! ## The same ramified prime globally and locally -/

/-- The global Gaussian prime above two. -/
def globalPi : L :=
  1 - N13SexticSquareclass.zeta

/-- Its square is a rational `2` times the Gaussian unit `-ζ`. -/
theorem globalPi_sq :
    globalPi ^ 2 =
      algebraMap ℚ L 2 * (-N13SexticSquareclass.zeta) := by
  change
    (1 - N13SexticSquareclass.zeta) ^ 2 =
      algebraMap ℚ L 2 * (-N13SexticSquareclass.zeta)
  calc
    _ =
        1 - 2 * N13SexticSquareclass.zeta +
          N13SexticSquareclass.zeta ^ 2 := by ring
    _ = _ := by
      rw [N13GaussianCubic.zeta_sq]
      change
        1 - 2 * N13SexticSquareclass.zeta + (-1) =
          (2 : L) * (-N13SexticSquareclass.zeta)
      ring

/-- Removing `2^m` from an even ramified power leaves `(-ζ)^m`. -/
theorem globalPi_even_pow (m : ℕ) :
    globalPi ^ (2 * m) =
      algebraMap ℚ L (2 ^ m : ℚ) *
        (-N13SexticSquareclass.zeta) ^ m := by
  calc
    globalPi ^ (2 * m) = (globalPi ^ 2) ^ m := by
      rw [pow_mul]
    _ =
        (algebraMap ℚ L 2 *
          (-N13SexticSquareclass.zeta)) ^ m := by
      rw [globalPi_sq]
    _ =
        (algebraMap ℚ L 2) ^ m *
          (-N13SexticSquareclass.zeta) ^ m := by
      rw [mul_pow]
    _ = _ := by rw [← map_pow]

@[simp] theorem globalPi_specializes :
    sexticToLocalOrder globalPi =
      algebraMap Order LocalOrder pi := by
  simp [globalPi, pi, localI]

/-! ## Exact integral normalization -/

/-- The unit `-i` left after dividing `π²` by the rational scalar `2`. -/
def negIUnit : Orderˣ where
  val := -i
  inv := i
  val_inv := by
    rw [neg_mul, ← pow_two, i_sq]
    simp
  inv_val := by
    rw [mul_neg, ← pow_two, i_sq]
    simp

@[simp] theorem negIUnit_val :
    (negIUnit : Order) = -i :=
  rfl

/-- The integral identity behind ramified valuation normalization. -/
theorem pi_even_pow (m : ℕ) :
    pi ^ (2 * m) = (2 : Order) ^ m * (negIUnit : Order) ^ m := by
  calc
    pi ^ (2 * m) = (pi ^ 2) ^ m := by rw [pow_mul]
    _ = (-(2 * i)) ^ m := by rw [pi_sq_eq]
    _ = ((2 : Order) * (-i)) ^ m := by
      congr 1
      ring
    _ = _ := by simp only [mul_pow, negIUnit_val]

/-- The correction unit has exactly the Gaussian torsion first jet. -/
theorem reduction_negIUnit :
    Units.map reduction.toMonoidHom negIUnit = zetaJet := by
  apply Units.ext
  change reduction (-i) = (zetaJet : DualNumber F8)
  rw [map_neg, reduction_i]
  have hnegone : (-1 : F8) = 1 := by
    calc
      (-1 : F8) = 1 - 2 := by ring
      _ = 1 := by rw [N13LocalDlogTwo.charTwo]; simp
  ext <;>
    simp [N13LocalDlogRegimes.gaussianIDual, zetaJet,
      RamifiedDlog.unitOf_val, hnegone]

/-- The normalized first jet of an even ramified power. -/
def ramifiedCorrectionJet (m : ℕ) : JetUnit :=
  Units.map reduction.toMonoidHom (negIUnit ^ m)

theorem ramifiedCorrectionJet_eq (m : ℕ) :
    ramifiedCorrectionJet m = zetaJet ^ m := by
  rw [ramifiedCorrectionJet, map_pow, reduction_negIUnit]

theorem dlog_ramifiedCorrectionJet (m : ℕ) :
    RamifiedDlog.dlog (ramifiedCorrectionJet m) = (m : F8) := by
  rw [ramifiedCorrectionJet_eq,
    N13GaussianCandidateDlog.dlog_pow_nat, dlog_zeta, mul_one]

/-! ## Absorbing the half-valuation into the candidate -/

/-- The first jet after normalizing a candidate with ramified valuation
`2m` by the rational scalar `2^m`. -/
def normalizedCandidateJet
    (m : ℕ) (a b c d : ZMod 2) : JetUnit :=
  ramifiedCorrectionJet m * candidateJet a b c d

theorem dlog_normalizedCandidateJet
    (m : ℕ) (a b c d : ZMod 2) :
    RamifiedDlog.dlog
        (normalizedCandidateJet m a b c d) =
      (m : F8) + candidateDlog a b c d := by
  rw [normalizedCandidateJet, RamifiedDlog.dlog_mul,
    dlog_ramifiedCorrectionJet, dlog_candidateJet]

/-- Only the parity of the half-valuation survives in the first jet. -/
theorem normalizedCandidateJet_eq_parityShift
    (m : ℕ) (a b c d : ZMod 2) :
    normalizedCandidateJet m a b c d =
      candidateJet (a + (m : ZMod 2)) b c d := by
  rw [normalizedCandidateJet, ramifiedCorrectionJet_eq]
  simp only [candidateJet]
  have hpow_mod_two (n : ℕ) :
      zetaJet ^ n = zetaJet ^ (n % 2) := by
    have hzetaSq : zetaJet ^ 2 = 1 := by
      apply Units.ext
      change
        (zetaJet : DualNumber F8) ^ 2 = 1
      ext <;>
        simp [zetaJet, RamifiedDlog.unitOf_val,
          N13LocalDlogTwo.charTwo]
    calc
      zetaJet ^ n =
          zetaJet ^ (n % 2 + 2 * (n / 2)) := by
        rw [Nat.mod_add_div]
      _ =
          zetaJet ^ (n % 2) *
            (zetaJet ^ 2) ^ (n / 2) := by
        rw [pow_add, pow_mul]
      _ = zetaJet ^ (n % 2) := by
        rw [hzetaSq, one_pow, mul_one]
  have hm :
      zetaJet ^ m =
        zetaJet ^ (m : ZMod 2).val := by
    simpa only [ZMod.val_natCast] using hpow_mod_two m
  have hadd :
      zetaJet ^ (m : ZMod 2).val *
          zetaJet ^ a.val =
        zetaJet ^ (a + (m : ZMod 2)).val := by
    rw [← pow_add, hpow_mod_two, ZMod.val_add]
    congr 2
    exact Nat.add_comm _ _
  rw [hm]
  calc
    zetaJet ^ (m : ZMod 2).val *
          (zetaJet ^ a.val * e1Jet ^ b.val *
            e2Jet ^ c.val * (aJet * qJet) ^ d.val) =
        (zetaJet ^ (m : ZMod 2).val *
            zetaJet ^ a.val) *
          e1Jet ^ b.val * e2Jet ^ c.val *
          (aJet * qJet) ^ d.val := by
      ac_rfl
    _ =
        zetaJet ^ (a + (m : ZMod 2)).val *
          e1Jet ^ b.val * e2Jet ^ c.val *
          (aJet * qJet) ^ d.val := by
      rw [hadd]

theorem dlog_normalizedCandidateJet_eq_shifted
    (m : ℕ) (a b c d : ZMod 2) :
    RamifiedDlog.dlog
        (normalizedCandidateJet m a b c d) =
      candidateDlog (a + (m : ZMod 2)) b c d := by
  rw [normalizedCandidateJet_eq_parityShift, dlog_candidateJet]

end

end MazurProof.N13GaussianRamifiedNormalization
