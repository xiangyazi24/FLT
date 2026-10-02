import FLT.Assumptions.MazurProof.N13SpecialSmallNumerator
import Mathlib.RingTheory.Coprime.Lemmas

/-!
Source pin: b07243d72093bec5686e15b1208cb50d000f3e8d.
Source-only repair of the certificate candidate from
4109ba77745784c1a9f8c4c7b304df4124bf5ac4. Lean and axiom checks NOT RUN.

Finite polynomial certificates for all 32 * 4 coefficient pairs in the
GOOD F2 model. Polynomial divisibility is never passed to a decision
procedure. The six local equations have explicit cofactors. Each of the
58 unsupported nonzero norms has an explicit factor coprime to both X
and X - 1; its two Bezout identities rule out support. The zero norm is
excluded separately. The 69 supported rows have explicit six-polynomial
normal forms and first-nonzero-coefficient certificates.

All public definition values and theorem statements are unchanged.
The link between these nine-jet orders and the six geometric local
orders is a separate theorem.
-/

namespace MazurProof.N13SpecialSmallFunctionCertificate

noncomputable section
open Polynomial

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

abbrev K := N13GoodModelTwo.F2

def numerator (a : Fin 5 → K) : K[X] := ∑ i : Fin 5, C (a i) * X ^ (i : ℕ)
def ordinate (b : Fin 2 → K) : K[X] := C (b 0) + C (b 1) * X

def jetZeroZero : K[X] := X ^ 4 + X ^ 7
def jetZeroOne : K[X] := 1 + X + X ^ 3 + X ^ 4 + X ^ 7
def jetOneZero : K[X] := X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8
def jetOneOne : K[X] := 1 + X + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8
def jetInfinityZero : K[X] := X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8
def jetInfinityOne : K[X] := 1 + X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8

def residual (H R s : K[X]) : K[X] := s ^ 2 + H * s - R

private theorem two_poly : (2 : K[X]) = 0 :=
  CharP.cast_eq_zero (K[X]) 2

/-- The displayed polynomials really satisfy all six local equations to
nine-jet precision. The divisibility witnesses are explicit polynomials. -/
theorem jet_polynomials_satisfy_equations :
    (X : K[X]) ^ 9 ∣ residual N13GoodCoordinateRingTwo.hPoly N13GoodCoordinateRingTwo.rhsPoly jetZeroZero ∧
    (X : K[X]) ^ 9 ∣ residual N13GoodCoordinateRingTwo.hPoly N13GoodCoordinateRingTwo.rhsPoly jetZeroOne ∧
    (X : K[X]) ^ 9 ∣ residual (N13GoodCoordinateRingTwo.hPoly.comp (X + 1))
      (N13GoodCoordinateRingTwo.rhsPoly.comp (X + 1)) jetOneZero ∧
    (X : K[X]) ^ 9 ∣ residual (N13GoodCoordinateRingTwo.hPoly.comp (X + 1))
      (N13GoodCoordinateRingTwo.rhsPoly.comp (X + 1)) jetOneOne ∧
    (X : K[X]) ^ 9 ∣ residual N13SpecialInfinityChart.hPoly N13SpecialInfinityChart.rhsPoly jetInfinityZero ∧
    (X : K[X]) ^ 9 ∣ residual N13SpecialInfinityChart.hPoly N13SpecialInfinityChart.rhsPoly jetInfinityOne := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨X + X ^ 5, ?_⟩
    norm_num [residual, N13GoodCoordinateRingTwo.hPoly,
      N13GoodCoordinateRingTwo.rhsPoly, N13SpecialInfinityChart.hPoly,
      N13SpecialInfinityChart.rhsPoly, jetZeroZero, jetZeroOne,
      jetOneZero, jetOneOne, jetInfinityZero, jetInfinityOne,
      Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.pow_comp] <;>
      linear_combination (X ^ 7 + X ^ 8 + X ^ 11) * two_poly
  · refine ⟨X + X ^ 5, ?_⟩
    norm_num [residual, N13GoodCoordinateRingTwo.hPoly,
      N13GoodCoordinateRingTwo.rhsPoly, N13SpecialInfinityChart.hPoly,
      N13SpecialInfinityChart.rhsPoly, jetZeroZero, jetZeroOne,
      jetOneZero, jetOneOne, jetInfinityZero, jetInfinityOne,
      Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.pow_comp] <;>
      linear_combination (1 + 2 * X + X ^ 2 + 2 * X ^ 3 + 3 * X ^ 4 + X ^ 5 + X ^ 6 + 3 * X ^ 7 + 2 * X ^ 8 + X ^ 10 + X ^ 11) * two_poly
  · refine ⟨1 + X ^ 2 + X ^ 3 + X ^ 7, ?_⟩
    norm_num [residual, N13GoodCoordinateRingTwo.hPoly,
      N13GoodCoordinateRingTwo.rhsPoly, N13SpecialInfinityChart.hPoly,
      N13SpecialInfinityChart.rhsPoly, jetZeroZero, jetZeroOne,
      jetOneZero, jetOneOne, jetInfinityZero, jetInfinityOne,
      Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.pow_comp] <;>
      linear_combination (-1 - 3 * X - 4 * X ^ 2 - X ^ 3 + 4 * X ^ 4 + 7 * X ^ 5 + 8 * X ^ 6 + 7 * X ^ 7 + 6 * X ^ 8 + 5 * X ^ 9 + 4 * X ^ 10 + 2 * X ^ 11 + X ^ 12 + X ^ 13 + X ^ 14) * two_poly
  · refine ⟨1 + X ^ 2 + X ^ 3 + X ^ 7, ?_⟩
    norm_num [residual, N13GoodCoordinateRingTwo.hPoly,
      N13GoodCoordinateRingTwo.rhsPoly, N13SpecialInfinityChart.hPoly,
      N13SpecialInfinityChart.rhsPoly, jetZeroZero, jetZeroOne,
      jetOneZero, jetOneOne, jetInfinityZero, jetInfinityOne,
      Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.pow_comp] <;>
      linear_combination (1 - 4 * X ^ 2 - 5 * X ^ 3 + 5 * X ^ 5 + 7 * X ^ 6 + 5 * X ^ 7 + 5 * X ^ 8 + 4 * X ^ 9 + 3 * X ^ 10 + X ^ 11 + X ^ 12 + X ^ 13 + X ^ 14) * two_poly
  · refine ⟨1 + X ^ 2 + X ^ 3 + X ^ 7, ?_⟩
    norm_num [residual, N13GoodCoordinateRingTwo.hPoly,
      N13GoodCoordinateRingTwo.rhsPoly, N13SpecialInfinityChart.hPoly,
      N13SpecialInfinityChart.rhsPoly, jetZeroZero, jetZeroOne,
      jetOneZero, jetOneOne, jetInfinityZero, jetInfinityOne,
      Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.pow_comp] <;>
      linear_combination (X ^ 3 + 2 * X ^ 4 + 2 * X ^ 5 + 3 * X ^ 6 + 3 * X ^ 7 + 3 * X ^ 8 + 3 * X ^ 9 + 2 * X ^ 10 + 2 * X ^ 11 + X ^ 12 + X ^ 13 + X ^ 14) * two_poly
  · refine ⟨1 + X ^ 2 + X ^ 3 + X ^ 7, ?_⟩
    norm_num [residual, N13GoodCoordinateRingTwo.hPoly,
      N13GoodCoordinateRingTwo.rhsPoly, N13SpecialInfinityChart.hPoly,
      N13SpecialInfinityChart.rhsPoly, jetZeroZero, jetZeroOne,
      jetOneZero, jetOneOne, jetInfinityZero, jetInfinityOne,
      Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
      Polynomial.pow_comp] <;>
      linear_combination (1 + X + 2 * X ^ 2 + 2 * X ^ 3 + 3 * X ^ 4 + 3 * X ^ 5 + 4 * X ^ 6 + 3 * X ^ 7 + 4 * X ^ 8 + 2 * X ^ 9 + 3 * X ^ 10 + X ^ 11 + X ^ 12 + X ^ 13 + X ^ 14) * two_poly

/-- First nonzero coefficient among 0,...,8; value9 means no such coefficient. -/
def jetOrder (p : K[X]) : ℕ :=
  (List.range 9).findIdx (fun n => decide (p.coeff n ≠ 0))

def infinityNumerator (a : Fin 5 → K) : K[X] := ∑ i : Fin 5, C (a i) * X ^ (4 - (i : ℕ))
def infinityOrdinate (b : Fin 2 → K) : K[X] := C (b 0) * X + C (b 1)

def sixJetPolynomials (a : Fin 5 → K) (b : Fin 2 → K) : Fin 6 → K[X] := ![
  numerator a + ordinate b * jetZeroZero,
  numerator a + ordinate b * jetZeroOne,
  (numerator a).comp (X + 1) + (ordinate b).comp (X + 1) * jetOneZero,
  (numerator a).comp (X + 1) + (ordinate b).comp (X + 1) * jetOneOne,
  infinityNumerator a + infinityOrdinate b * jetInfinityZero,
  infinityNumerator a + infinityOrdinate b * jetInfinityOne]

def sixJetOrders (a : Fin 5 → K) (b : Fin 2 → K) (i : Fin 6) : ℕ :=
  jetOrder (sixJetPolynomials a b i)

def weightedJetCode (a : Fin 5 → K) (b : Fin 2 → K) : ZMod 19 :=
  (sixJetOrders a b 0 : ZMod 19) - sixJetOrders a b 1 +
    7 * (sixJetOrders a b 2 : ZMod 19) - 7 * sixJetOrders a b 3 +
    8 * (sixJetOrders a b 4 : ZMod 19) - 8 * sixJetOrders a b 5


/-- A first nonzero coefficient below nine determines `jetOrder`.
This is a proved bridge from finite coefficient data to `List.findIdx`. -/
private theorem jetOrder_of_coefficients (p : K[X]) (n : ℕ) (hn : n < 9)
    (hne : p.coeff n ≠ 0)
    (hzero : ∀ j : Fin 9, (j : ℕ) < n → p.coeff j = 0) :
    jetOrder p = n := by
  unfold jetOrder
  apply (List.findIdx_eq (xs := List.range 9) (i := n) (by simpa using hn)).2
  constructor
  · simpa using hne
  · intro j hj
    have hz := hzero ⟨j, hj.trans hn⟩ hj
    simpa using hz

private def GoodJets (p : Fin 6 → K[X]) : Prop :=
  (∀ i : Fin 6, jetOrder (p i) < 9 ∧
    (p i).coeff (jetOrder (p i)) ≠ 0 ∧
    ∀ j : Fin 9, (j : ℕ) < jetOrder (p i) → (p i).coeff j = 0) ∧
  (jetOrder (p 0) : ZMod 19) - jetOrder (p 1) +
    7 * (jetOrder (p 2) : ZMod 19) - 7 * jetOrder (p 3) +
    8 * (jetOrder (p 4) : ZMod 19) - 8 * jetOrder (p 5) = 0

private theorem goodJets_of_coefficients (p : Fin 6 → K[X]) (n : Fin 6 → ℕ)
    (hlt : ∀ i, n i < 9)
    (hne : ∀ i, (p i).coeff (n i) ≠ 0)
    (hzero : ∀ i, ∀ j : Fin 9, (j : ℕ) < n i → (p i).coeff j = 0)
    (hcode : (n 0 : ZMod 19) - n 1 + 7 * (n 2 : ZMod 19) - 7 * n 3 +
      8 * (n 4 : ZMod 19) - 8 * n 5 = 0) : GoodJets p := by
  have ho (i : Fin 6) : jetOrder (p i) = n i :=
    jetOrder_of_coefficients (p i) (n i) (hlt i) (hne i) (hzero i)
  constructor
  · intro i
    rw [ho i]
    exact ⟨hlt i, hne i, hzero i⟩
  · simpa only [ho] using hcode

private def PairCertificate (a : Fin 5 → K) (b : Fin 2 → K) : Prop :=
  N13SpecialAffineNorm.normPolynomial (numerator a) (ordinate b) ∣
    (X : K[X]) ^ 16 * (X - 1) ^ 16 → GoodJets (sixJetPolynomials a b)

/-- Two explicit Bezout identities exclude a monic nonconstant factor. -/
private theorem obstruction (f u v : K[X]) (hm : f.Monic) (hne : f ≠ 1)
    (hx : f + u * X = 1) (hx1 : f + v * (X - 1) = 1) :
    ¬ f ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  have h0 : IsCoprime f X := ⟨1, u, by simpa only [one_mul] using hx⟩
  have h1 : IsCoprime f (X - 1) := ⟨1, v, by simpa only [one_mul] using hx1⟩
  have hc : IsCoprime f ((X : K[X]) ^ 16 * (X - 1) ^ 16) :=
    h0.pow_right.mul_right h1.pow_right
  intro hd
  exact hne (hm.eq_one_of_isUnit (hc.isUnit_of_dvd hd))

private theorem obstruction_11 :
    ¬ (1 + X + X ^ 3 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (1 + X ^ 2) (X + X ^ 2)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 3) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X + X ^ 3) * two_poly
  · linear_combination (X ^ 3) * two_poly

private theorem obstruction_21 :
    ¬ (1 + X ^ 2 + X ^ 4 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X + X ^ 3) (X ^ 2 + X ^ 3)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 4) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 2 + X ^ 4) * two_poly
  · linear_combination (X ^ 4) * two_poly

private theorem obstruction_37 :
    ¬ (1 + X ^ 2 + X ^ 5 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X + X ^ 4) (X ^ 2 + X ^ 3 + X ^ 4)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 5) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 2 + X ^ 5) * two_poly
  · linear_combination (X ^ 5) * two_poly

private theorem obstruction_59 :
    ¬ (1 + X + X ^ 3 + X ^ 4 + X ^ 5 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (1 + X ^ 2 + X ^ 3 + X ^ 4) (X + X ^ 2 + X ^ 4)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 5) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X + X ^ 3 + X ^ 4 + X ^ 5) * two_poly
  · linear_combination (X ^ 3 + X ^ 5) * two_poly

private theorem obstruction_61 :
    ¬ (1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X + X ^ 2 + X ^ 3 + X ^ 4) (X ^ 2 + X ^ 4)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 5) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5) * two_poly
  · linear_combination (X ^ 3 + X ^ 5) * two_poly

private theorem obstruction_67 :
    ¬ (1 + X + X ^ 6 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (1 + X ^ 5) (X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 6) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X + X ^ 6) * two_poly
  · linear_combination (X ^ 6) * two_poly

private theorem obstruction_69 :
    ¬ (1 + X ^ 2 + X ^ 6 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X + X ^ 5) (X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 6) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 2 + X ^ 6) * two_poly
  · linear_combination (X ^ 6) * two_poly

private theorem obstruction_73 :
    ¬ (1 + X ^ 3 + X ^ 6 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X ^ 2 + X ^ 5) (X ^ 3 + X ^ 4 + X ^ 5)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 6) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 3 + X ^ 6) * two_poly
  · linear_combination (X ^ 6) * two_poly

private theorem obstruction_81 :
    ¬ (1 + X ^ 4 + X ^ 6 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X ^ 3 + X ^ 5) (X ^ 4 + X ^ 5)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 6) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 4 + X ^ 6) * two_poly
  · linear_combination (X ^ 6) * two_poly

private theorem obstruction_91 :
    ¬ (1 + X + X ^ 3 + X ^ 4 + X ^ 6 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (1 + X ^ 2 + X ^ 3 + X ^ 5) (X + X ^ 2 + X ^ 4 + X ^ 5)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 6) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X + X ^ 3 + X ^ 4 + X ^ 6) * two_poly
  · linear_combination (X ^ 3 + X ^ 6) * two_poly

private theorem obstruction_103 :
    ¬ (1 + X + X ^ 2 + X ^ 5 + X ^ 6 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (1 + X + X ^ 4 + X ^ 5) (X + X ^ 5)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 6) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X + X ^ 2 + X ^ 5 + X ^ 6) * two_poly
  · linear_combination (X ^ 2 + X ^ 6) * two_poly

private theorem obstruction_109 :
    ¬ (1 + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X + X ^ 2 + X ^ 4 + X ^ 5) (X ^ 2 + X ^ 5)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 6) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6) * two_poly
  · linear_combination (X ^ 3 + X ^ 6) * two_poly

private theorem obstruction_117 :
    ¬ (1 + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X + X ^ 3 + X ^ 4 + X ^ 5) (X ^ 2 + X ^ 3 + X ^ 5)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 6) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
  · linear_combination (X ^ 4 + X ^ 6) * two_poly

private theorem obstruction_261 :
    ¬ (1 + X ^ 2 + X ^ 8 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X + X ^ 7) (X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 8) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 2 + X ^ 8) * two_poly
  · linear_combination (X ^ 8) * two_poly

private theorem obstruction_273 :
    ¬ (1 + X ^ 4 + X ^ 8 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X ^ 3 + X ^ 7) (X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 8) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 4 + X ^ 8) * two_poly
  · linear_combination (X ^ 8) * two_poly

private theorem obstruction_321 :
    ¬ (1 + X ^ 6 + X ^ 8 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X ^ 5 + X ^ 7) (X ^ 6 + X ^ 7)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 8) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 6 + X ^ 8) * two_poly
  · linear_combination (X ^ 8) * two_poly

private theorem obstruction_341 :
    ¬ (1 + X ^ 2 + X ^ 4 + X ^ 6 + X ^ 8 : K[X]) ∣ (X : K[X]) ^ 16 * (X - 1) ^ 16 := by
  apply obstruction _ (X + X ^ 3 + X ^ 5 + X ^ 7) (X ^ 2 + X ^ 3 + X ^ 6 + X ^ 7)
  · monicity <;> norm_num
  · intro h
    have hc := congrArg (fun p : K[X] => p.coeff 8) h
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  · linear_combination (X ^ 2 + X ^ 4 + X ^ 6 + X ^ 8) * two_poly
  · linear_combination (X ^ 4 + X ^ 8) * two_poly

-- Coefficient bit codes (a, b) = (0, 0).
private theorem row_0_0 : PairCertificate ![0, 0, 0, 0, 0] ![0, 0] := by
  intro h
  have hn : N13SpecialAffineNorm.normPolynomial
      (numerator ![0, 0, 0, 0, 0]) (ordinate ![0, 0]) = 0 := by
    simp [N13SpecialAffineNorm.normPolynomial, numerator, ordinate, Fin.sum_univ_succ]
  rw [hn, zero_dvd_iff] at h
  have hx1 : (X : K[X]) - 1 ≠ 0 := by
    simpa using (Polynomial.X_sub_C_ne_zero (1 : K))
  exact False.elim ((mul_ne_zero (pow_ne_zero 16 Polynomial.X_ne_zero)
    (pow_ne_zero 16 hx1)) h)

-- Coefficient bit codes (a, b) = (0, 1).
private theorem row_0_1 : PairCertificate ![0, 0, 0, 0, 0] ![1, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 0, 0, 0] ![1, 0] =
    ![X ^ 4 + X ^ 7,
      1 + X + X ^ 3 + X ^ 4 + X ^ 7,
      X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
  rw [hp]
  apply goodJets_of_coefficients _ ![4, 0, 1, 0, 2, 1]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (0, 2).
private theorem row_0_2 : PairCertificate ![0, 0, 0, 0, 0] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 0, 0, 0] ![0, 1] =
    ![X ^ 5 + X ^ 8,
      X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 8,
      X + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X ^ 2 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
  rw [hp]
  apply goodJets_of_coefficients _ ![5, 1, 1, 0, 1, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (0, 3).
private theorem row_0_3 : PairCertificate ![0, 0, 0, 0, 0] ![1, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 0, 0, 0] ![1, 1] =
    ![X ^ 4 + X ^ 5 + X ^ 7 + X ^ 8,
      1 + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 7 + X ^ 8,
      X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X + X ^ 2 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X + X ^ 2 + X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 5 + X ^ 6) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![4, 0, 2, 1, 1, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (1, 0).
private theorem row_1_0 : PairCertificate ![1, 0, 0, 0, 0] ![0, 0] := by
  intro _
  have hp : sixJetPolynomials ![1, 0, 0, 0, 0] ![0, 0] =
    ![1,
      1,
      1,
      1,
      X ^ 4,
      X ^ 4] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 0, 0, 0, 4, 4]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (1, 1).
private theorem row_1_1 : PairCertificate ![1, 0, 0, 0, 0] ![1, 0] := by
  intro h
  have hf : (1 + X + X ^ 3 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 0, 0, 0, 0]) (ordinate ![1, 0]) := by
    refine ⟨X + X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - X ^ 3 - X ^ 4 - X ^ 5) * two_poly
  exact False.elim (obstruction_11 (hf.trans h))

-- Coefficient bit codes (a, b) = (1, 2).
private theorem row_1_2 : PairCertificate ![1, 0, 0, 0, 0] ![0, 1] := by
  intro h
  have hf : (1 + X + X ^ 3 + X ^ 4 + X ^ 5 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 0, 0, 0, 0]) (ordinate ![0, 1]) := by
    refine ⟨1 + X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - X ^ 3 - X ^ 4 - X ^ 5 - X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_59 (hf.trans h))

-- Coefficient bit codes (a, b) = (1, 3).
private theorem row_1_3 : PairCertificate ![1, 0, 0, 0, 0] ![1, 1] := by
  intro h
  have hf : (1 + X + X ^ 3 + X ^ 4 + X ^ 5 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 0, 0, 0, 0]) (ordinate ![1, 1]) := by
    refine ⟨X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - X ^ 3 - X ^ 4 - 2 * X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_59 (hf.trans h))

-- Coefficient bit codes (a, b) = (2, 0).
private theorem row_2_0 : PairCertificate ![0, 1, 0, 0, 0] ![0, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 0, 0, 0] ![0, 0] =
    ![X,
      X,
      1 + X,
      1 + X,
      X ^ 3,
      X ^ 3] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 1, 0, 0, 3, 3]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (2, 1).
private theorem row_2_1 : PairCertificate ![0, 1, 0, 0, 0] ![1, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 0, 0, 0] ![1, 0] =
    ![X + X ^ 4 + X ^ 7,
      1 + X ^ 3 + X ^ 4 + X ^ 7,
      1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X + X ^ 2 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 3) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 0, 0, 4, 2, 1]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (2, 2).
private theorem row_2_2 : PairCertificate ![0, 1, 0, 0, 0] ![0, 1] := by
  intro h
  have hf : (1 + X + X ^ 3 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 1, 0, 0, 0]) (ordinate ![0, 1]) := by
    refine ⟨X ^ 3 + X ^ 4, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X ^ 3 - X ^ 4 - X ^ 5 - X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_11 (hf.trans h))

-- Coefficient bit codes (a, b) = (2, 3).
private theorem row_2_3 : PairCertificate ![0, 1, 0, 0, 0] ![1, 1] := by
  intro h
  have hf : (1 + X + X ^ 2 + X ^ 5 + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 1, 0, 0, 0]) (ordinate ![1, 1]) := by
    refine ⟨X, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - X ^ 3 - X ^ 4 - 2 * X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_103 (hf.trans h))

-- Coefficient bit codes (a, b) = (3, 0).
private theorem row_3_0 : PairCertificate ![1, 1, 0, 0, 0] ![0, 0] := by
  intro _
  have hp : sixJetPolynomials ![1, 1, 0, 0, 0] ![0, 0] =
    ![1 + X,
      1 + X,
      X,
      X,
      X ^ 3 + X ^ 4,
      X ^ 3 + X ^ 4] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 0, 1, 1, 3, 3]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (3, 1).
private theorem row_3_1 : PairCertificate ![1, 1, 0, 0, 0] ![1, 0] := by
  intro _
  have hp : sixJetPolynomials ![1, 1, 0, 0, 0] ![1, 0] =
    ![1 + X + X ^ 4 + X ^ 7,
      X ^ 3 + X ^ 4 + X ^ 7,
      X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 3) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 3, 2, 0, 2, 1]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (3, 2).
private theorem row_3_2 : PairCertificate ![1, 1, 0, 0, 0] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![1, 1, 0, 0, 0] ![0, 1] =
    ![1 + X + X ^ 5 + X ^ 8,
      1 + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 8,
      X ^ 7 + X ^ 8 + X ^ 9,
      1 + X + X ^ 2 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 8] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 0, 7, 0, 1, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (3, 3).
private theorem row_3_3 : PairCertificate ![1, 1, 0, 0, 0] ![1, 1] := by
  intro h
  have hf : (1 + X + X ^ 3 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 0, 0, 0]) (ordinate ![1, 1]) := by
    refine ⟨X + X ^ 2 + X ^ 3 + X ^ 4, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - 2 * X ^ 2 - 2 * X ^ 3 - 3 * X ^ 4 - 3 * X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_11 (hf.trans h))

-- Coefficient bit codes (a, b) = (4, 0).
private theorem row_4_0 : PairCertificate ![0, 0, 1, 0, 0] ![0, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 1, 0, 0] ![0, 0] =
    ![X ^ 2,
      X ^ 2,
      1 + X ^ 2,
      1 + X ^ 2,
      X ^ 2,
      X ^ 2] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
  rw [hp]
  apply goodJets_of_coefficients _ ![2, 2, 0, 0, 2, 2]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (4, 1).
private theorem row_4_1 : PairCertificate ![0, 0, 1, 0, 0] ![1, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 1, 0, 0] ![1, 0] =
    ![X ^ 2 + X ^ 4 + X ^ 7,
      1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 7,
      1 + X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![2, 0, 0, 1, 4, 1]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (4, 2).
private theorem row_4_2 : PairCertificate ![0, 0, 1, 0, 0] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 1, 0, 0] ![0, 1] =
    ![X ^ 2 + X ^ 5 + X ^ 8,
      X + X ^ 4 + X ^ 5 + X ^ 8,
      1 + X + X ^ 2 + X ^ 7 + X ^ 8 + X ^ 9,
      X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + X ^ 2 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![2, 1, 0, 4, 1, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (4, 3).
private theorem row_4_3 : PairCertificate ![0, 0, 1, 0, 0] ![1, 1] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 5 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 0, 1, 0, 0]) (ordinate ![1, 1]) := by
    refine ⟨X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X ^ 2 - X ^ 3 - X ^ 4 - 2 * X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_37 (hf.trans h))

-- Coefficient bit codes (a, b) = (5, 0).
private theorem row_5_0 : PairCertificate ![1, 0, 1, 0, 0] ![0, 0] := by
  intro _
  have hp : sixJetPolynomials ![1, 0, 1, 0, 0] ![0, 0] =
    ![1 + X ^ 2,
      1 + X ^ 2,
      X ^ 2,
      X ^ 2,
      X ^ 2 + X ^ 4,
      X ^ 2 + X ^ 4] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 0, 2, 2, 2, 2]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (5, 1).
private theorem row_5_1 : PairCertificate ![1, 0, 1, 0, 0] ![1, 0] := by
  intro _
  have hp : sixJetPolynomials ![1, 0, 1, 0, 0] ![1, 0] =
    ![1 + X ^ 2 + X ^ 4 + X ^ 7,
      X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 7,
      X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 1, 1, 0, 5, 1]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (5, 2).
private theorem row_5_2 : PairCertificate ![1, 0, 1, 0, 0] ![0, 1] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 0, 1, 0, 0]) (ordinate ![0, 1]) := by
    refine ⟨1 + X, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 3 - X ^ 4 - X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_117 (hf.trans h))

-- Coefficient bit codes (a, b) = (5, 3).
private theorem row_5_3 : PairCertificate ![1, 0, 1, 0, 0] ![1, 1] := by
  intro _
  have hp : sixJetPolynomials ![1, 0, 1, 0, 0] ![1, 1] =
    ![1 + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 7 + X ^ 8,
      X ^ 3 + X ^ 5 + X ^ 7 + X ^ 8,
      X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X + X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X ^ 2 + X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + 2 * X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 2 * X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 3, 3, 1, 1, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (6, 0).
private theorem row_6_0 : PairCertificate ![0, 1, 1, 0, 0] ![0, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 1, 0, 0] ![0, 0] =
    ![X + X ^ 2,
      X + X ^ 2,
      X + X ^ 2,
      X + X ^ 2,
      X ^ 2 + X ^ 3,
      X ^ 2 + X ^ 3] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 1, 1, 1, 2, 2]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (6, 1).
private theorem row_6_1 : PairCertificate ![0, 1, 1, 0, 0] ![1, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 1, 0, 0] ![1, 0] =
    ![X + X ^ 2 + X ^ 4 + X ^ 7,
      1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 7,
      X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2 + X ^ 3) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 0, 3, 0, 3, 1]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (6, 2).
private theorem row_6_2 : PairCertificate ![0, 1, 1, 0, 0] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 1, 0, 0] ![0, 1] =
    ![X + X ^ 2 + X ^ 5 + X ^ 8,
      X ^ 4 + X ^ 5 + X ^ 8,
      X ^ 2 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + X ^ 2 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 4, 2, 0, 1, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (6, 3).
private theorem row_6_3 : PairCertificate ![0, 1, 1, 0, 0] ![1, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 1, 0, 0] ![1, 1] =
    ![X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 7 + X ^ 8,
      1 + X + X ^ 3 + X ^ 5 + X ^ 7 + X ^ 8,
      X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X ^ 2 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + 2 * X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 3 * X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 0, 1, 5, 1, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (7, 0).
private theorem row_7_0 : PairCertificate ![1, 1, 1, 0, 0] ![0, 0] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 4 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 1, 0, 0]) (ordinate ![0, 0]) := by
    refine ⟨1, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (X + X ^ 2 + X ^ 3) * two_poly
  exact False.elim (obstruction_21 (hf.trans h))

-- Coefficient bit codes (a, b) = (7, 1).
private theorem row_7_1 : PairCertificate ![1, 1, 1, 0, 0] ![1, 0] := by
  intro _
  have hp : sixJetPolynomials ![1, 1, 1, 0, 0] ![1, 0] =
    ![1 + X + X ^ 2 + X ^ 4 + X ^ 7,
      X ^ 2 + X ^ 3 + X ^ 4 + X ^ 7,
      1 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 2 * X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2 + X ^ 3) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 2, 0, 2, 3, 1]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (7, 2).
private theorem row_7_2 : PairCertificate ![1, 1, 1, 0, 0] ![0, 1] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 1, 0, 0]) (ordinate ![0, 1]) := by
    refine ⟨1 + X, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X ^ 3 - X ^ 4 - X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_109 (hf.trans h))

-- Coefficient bit codes (a, b) = (7, 3).
private theorem row_7_3 : PairCertificate ![1, 1, 1, 0, 0] ![1, 1] := by
  intro h
  have hf : (1 + X + X ^ 3 + X ^ 4 + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 1, 0, 0]) (ordinate ![1, 1]) := by
    refine ⟨X, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - X ^ 3 - 2 * X ^ 4 - 3 * X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_91 (hf.trans h))

-- Coefficient bit codes (a, b) = (8, 0).
private theorem row_8_0 : PairCertificate ![0, 0, 0, 1, 0] ![0, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 0, 1, 0] ![0, 0] =
    ![X ^ 3,
      X ^ 3,
      1 + X + X ^ 2 + X ^ 3,
      1 + X + X ^ 2 + X ^ 3,
      X,
      X] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
  rw [hp]
  apply goodJets_of_coefficients _ ![3, 3, 0, 0, 1, 1]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (8, 1).
private theorem row_8_1 : PairCertificate ![0, 0, 0, 1, 0] ![1, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 0, 1, 0] ![1, 0] =
    ![X ^ 3 + X ^ 4 + X ^ 7,
      1 + X + X ^ 4 + X ^ 7,
      1 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 * X + 2 * X ^ 2 + X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![3, 0, 0, 2, 1, 2]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (8, 2).
private theorem row_8_2 : PairCertificate ![0, 0, 0, 1, 0] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 0, 1, 0] ![0, 1] =
    ![X ^ 3 + X ^ 5 + X ^ 8,
      X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 8,
      1 + X ^ 2 + X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9,
      X + X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 * X + 2 * X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + 2 * X ^ 2 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![3, 1, 0, 1, 3, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (8, 3).
private theorem row_8_3 : PairCertificate ![0, 0, 0, 1, 0] ![1, 1] := by
  intro h
  have hf : (1 + X + X ^ 3 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 0, 0, 1, 0]) (ordinate ![1, 1]) := by
    refine ⟨X ^ 3, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X ^ 3 - 2 * X ^ 4 - 2 * X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_11 (hf.trans h))

-- Coefficient bit codes (a, b) = (9, 0).
private theorem row_9_0 : PairCertificate ![1, 0, 0, 1, 0] ![0, 0] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 4 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 0, 0, 1, 0]) (ordinate ![0, 0]) := by
    refine ⟨1 + X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X ^ 2 + X ^ 3 - X ^ 4) * two_poly
  exact False.elim (obstruction_21 (hf.trans h))

-- Coefficient bit codes (a, b) = (9, 1).
private theorem row_9_1 : PairCertificate ![1, 0, 0, 1, 0] ![1, 0] := by
  intro _
  have hp : sixJetPolynomials ![1, 0, 0, 1, 0] ![1, 0] =
    ![1 + X ^ 3 + X ^ 4 + X ^ 7,
      X + X ^ 4 + X ^ 7,
      X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X + X ^ 2 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + 2 * X ^ 2 + X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 1, 4, 0, 1, 2]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (9, 2).
private theorem row_9_2 : PairCertificate ![1, 0, 0, 1, 0] ![0, 1] := by
  intro h
  have hf : (1 + X + X ^ 3 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 0, 0, 1, 0]) (ordinate ![0, 1]) := by
    refine ⟨1 + X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - X ^ 4 - X ^ 5 - X ^ 7) * two_poly
  exact False.elim (obstruction_11 (hf.trans h))

-- Coefficient bit codes (a, b) = (9, 3).
private theorem row_9_3 : PairCertificate ![1, 0, 0, 1, 0] ![1, 1] := by
  intro _
  have hp : sixJetPolynomials ![1, 0, 0, 1, 0] ![1, 1] =
    ![1 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 7 + X ^ 8,
      X ^ 2 + X ^ 5 + X ^ 7 + X ^ 8,
      X + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 2 + X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X + X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + 3 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 3 * X + 2 * X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 2, 1, 3, 2, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (10, 0).
private theorem row_10_0 : PairCertificate ![0, 1, 0, 1, 0] ![0, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 0, 1, 0] ![0, 0] =
    ![X + X ^ 3,
      X + X ^ 3,
      X ^ 2 + X ^ 3,
      X ^ 2 + X ^ 3,
      X + X ^ 3,
      X + X ^ 3] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 1, 2, 2, 1, 1]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (10, 1).
private theorem row_10_1 : PairCertificate ![0, 1, 0, 1, 0] ![1, 0] := by
  intro h
  have hf : (1 + X + X ^ 3 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 1, 0, 1, 0]) (ordinate ![1, 0]) := by
    refine ⟨X + X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - X ^ 3 - X ^ 4 - X ^ 5) * two_poly
  exact False.elim (obstruction_11 (hf.trans h))

-- Coefficient bit codes (a, b) = (10, 2).
private theorem row_10_2 : PairCertificate ![0, 1, 0, 1, 0] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 0, 1, 0] ![0, 1] =
    ![X + X ^ 3 + X ^ 5 + X ^ 8,
      X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 8,
      X + X ^ 2 + X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + 2 * X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 2 * X ^ 2 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 2, 1, 0, 4, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (10, 3).
private theorem row_10_3 : PairCertificate ![0, 1, 0, 1, 0] ![1, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 0, 1, 0] ![1, 1] =
    ![X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 7 + X ^ 8,
      1 + X + X ^ 2 + X ^ 5 + X ^ 7 + X ^ 8,
      X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 2 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 3 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 3 * X + 2 * X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 0, 4, 1, 2, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (11, 0).
private theorem row_11_0 : PairCertificate ![1, 1, 0, 1, 0] ![0, 0] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 0, 1, 0]) (ordinate ![0, 0]) := by
    refine ⟨1, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (X + X ^ 3 + X ^ 4) * two_poly
  exact False.elim (obstruction_69 (hf.trans h))

-- Coefficient bit codes (a, b) = (11, 1).
private theorem row_11_1 : PairCertificate ![1, 1, 0, 1, 0] ![1, 0] := by
  intro _
  have hp : sixJetPolynomials ![1, 1, 0, 1, 0] ![1, 0] =
    ![1 + X + X ^ 3 + X ^ 4 + X ^ 7,
      X ^ 4 + X ^ 7,
      1 + X + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + 2 * X ^ 2 + X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 2 * X + X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 3) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 4, 0, 1, 1, 2]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (11, 2).
private theorem row_11_2 : PairCertificate ![1, 1, 0, 1, 0] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![1, 1, 0, 1, 0] ![0, 1] =
    ![1 + X + X ^ 3 + X ^ 5 + X ^ 8,
      1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 8,
      1 + X + X ^ 2 + X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9,
      X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X ^ 5 + X ^ 6 + X ^ 8,
      1 + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 8] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + 2 * X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 3 * X + 2 * X ^ 2 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 4) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 0, 0, 3, 5, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (11, 3).
private theorem row_11_3 : PairCertificate ![1, 1, 0, 1, 0] ![1, 1] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 0, 1, 0]) (ordinate ![1, 1]) := by
    refine ⟨X, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - X ^ 3 - 2 * X ^ 4 - 3 * X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_61 (hf.trans h))

-- Coefficient bit codes (a, b) = (12, 0).
private theorem row_12_0 : PairCertificate ![0, 0, 1, 1, 0] ![0, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 1, 1, 0] ![0, 0] =
    ![X ^ 2 + X ^ 3,
      X ^ 2 + X ^ 3,
      X + X ^ 3,
      X + X ^ 3,
      X + X ^ 2,
      X + X ^ 2] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + 2 * X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + 2 * X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
  rw [hp]
  apply goodJets_of_coefficients _ ![2, 2, 1, 1, 1, 1]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (12, 1).
private theorem row_12_1 : PairCertificate ![0, 0, 1, 1, 0] ![1, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 1, 1, 0] ![1, 0] =
    ![X ^ 2 + X ^ 3 + X ^ 4 + X ^ 7,
      1 + X + X ^ 2 + X ^ 4 + X ^ 7,
      X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 2 * X ^ 2 + X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 2 * X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![2, 0, 2, 0, 1, 3]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (12, 2).
private theorem row_12_2 : PairCertificate ![0, 0, 1, 1, 0] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 1, 1, 0] ![0, 1] =
    ![X ^ 2 + X ^ 3 + X ^ 5 + X ^ 8,
      X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 8,
      X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 3 * X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 2 * X ^ 2 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![2, 1, 3, 0, 2, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (12, 3).
private theorem row_12_3 : PairCertificate ![0, 0, 1, 1, 0] ![1, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 1, 1, 0] ![1, 1] =
    ![X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 7 + X ^ 8,
      1 + X ^ 5 + X ^ 7 + X ^ 8,
      X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 3 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 4 * X + 2 * X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 5 + X ^ 6) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![2, 0, 1, 2, 3, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (13, 0).
private theorem row_13_0 : PairCertificate ![1, 0, 1, 1, 0] ![0, 0] := by
  intro h
  have hf : (1 + X ^ 4 + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 0, 1, 1, 0]) (ordinate ![0, 0]) := by
    refine ⟨1, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (X ^ 2 + X ^ 3 + X ^ 5) * two_poly
  exact False.elim (obstruction_81 (hf.trans h))

-- Coefficient bit codes (a, b) = (13, 1).
private theorem row_13_1 : PairCertificate ![1, 0, 1, 1, 0] ![1, 0] := by
  intro _
  have hp : sixJetPolynomials ![1, 0, 1, 1, 0] ![1, 0] =
    ![1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 7,
      X + X ^ 2 + X ^ 4 + X ^ 7,
      1 + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 2 * X ^ 2 + X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 3 * X + 2 * X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 1, 0, 3, 1, 3]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (13, 2).
private theorem row_13_2 : PairCertificate ![1, 0, 1, 1, 0] ![0, 1] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 5 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 0, 1, 1, 0]) (ordinate ![0, 1]) := by
    refine ⟨1 + X, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 4 - X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_37 (hf.trans h))

-- Coefficient bit codes (a, b) = (13, 3).
private theorem row_13_3 : PairCertificate ![1, 0, 1, 1, 0] ![1, 1] := by
  intro _
  have hp : sixJetPolynomials ![1, 0, 1, 1, 0] ![1, 1] =
    ![1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 7 + X ^ 8,
      X ^ 5 + X ^ 7 + X ^ 8,
      1 + X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      1 + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X + X ^ 2 + X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2 + X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 3 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 4 * X + 2 * X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 5, 0, 0, 3, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (14, 0).
private theorem row_14_0 : PairCertificate ![0, 1, 1, 1, 0] ![0, 0] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 4 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 1, 1, 1, 0]) (ordinate ![0, 0]) := by
    refine ⟨X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (X ^ 3 + X ^ 4 + X ^ 5) * two_poly
  exact False.elim (obstruction_21 (hf.trans h))

-- Coefficient bit codes (a, b) = (14, 1).
private theorem row_14_1 : PairCertificate ![0, 1, 1, 1, 0] ![1, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 1, 1, 0] ![1, 0] =
    ![X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 7,
      1 + X ^ 2 + X ^ 4 + X ^ 7,
      1 + X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 2 * X ^ 2 + X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 3 * X + 2 * X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 3) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 0, 0, 1, 1, 5]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (14, 2).
private theorem row_14_2 : PairCertificate ![0, 1, 1, 1, 0] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 1, 1, 0] ![0, 1] =
    ![X + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 8,
      X ^ 3 + X ^ 4 + X ^ 5 + X ^ 8,
      1 + X + X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9,
      X ^ 2 + X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 3 * X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 4 * X + 2 * X ^ 2 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 3, 0, 2, 2, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (14, 3).
private theorem row_14_3 : PairCertificate ![0, 1, 1, 1, 0] ![1, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 1, 1, 0] ![1, 1] =
    ![X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 7 + X ^ 8,
      1 + X + X ^ 5 + X ^ 7 + X ^ 8,
      1 + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      1 + X + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 7 + X ^ 8 + X ^ 9,
      1 + X + X ^ 2 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 4 * X + 3 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 4 * X + 2 * X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 0, 0, 0, 7, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (15, 0).
private theorem row_15_0 : PairCertificate ![1, 1, 1, 1, 0] ![0, 0] := by
  intro _
  have hp : sixJetPolynomials ![1, 1, 1, 1, 0] ![0, 0] =
    ![1 + X + X ^ 2 + X ^ 3,
      1 + X + X ^ 2 + X ^ 3,
      X ^ 3,
      X ^ 3,
      X + X ^ 2 + X ^ 3 + X ^ 4,
      X + X ^ 2 + X ^ 3 + X ^ 4] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 3 * X + 2 * X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 3 * X + 2 * X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 0, 3, 3, 1, 1]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (15, 1).
private theorem row_15_1 : PairCertificate ![1, 1, 1, 1, 0] ![1, 0] := by
  intro _
  have hp : sixJetPolynomials ![1, 1, 1, 1, 0] ![1, 0] =
    ![1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 7,
      X ^ 2 + X ^ 4 + X ^ 7,
      X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 3 * X + 2 * X ^ 2 + X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 3 * X + 2 * X ^ 2) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 3) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 2, 1, 0, 1, 4]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (15, 2).
private theorem row_15_2 : PairCertificate ![1, 1, 1, 1, 0] ![0, 1] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 1, 1, 0]) (ordinate ![0, 1]) := by
    refine ⟨1 + X, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X ^ 4 - X ^ 5 - X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_61 (hf.trans h))

-- Coefficient bit codes (a, b) = (15, 3).
private theorem row_15_3 : PairCertificate ![1, 1, 1, 1, 0] ![1, 1] := by
  intro _
  have hp : sixJetPolynomials ![1, 1, 1, 1, 0] ![1, 1] =
    ![1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 7 + X ^ 8,
      X + X ^ 5 + X ^ 7 + X ^ 8,
      X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X + X ^ 2 + X ^ 7 + X ^ 8 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2 + X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 4 * X + 3 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (3 + 4 * X + 2 * X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 1, 2, 1, 4, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (16, 0).
private theorem row_16_0 : PairCertificate ![0, 0, 0, 0, 1] ![0, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 0, 0, 1] ![0, 0] =
    ![X ^ 4,
      X ^ 4,
      1 + X ^ 4,
      1 + X ^ 4,
      1,
      1] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 * X + 3 * X ^ 2 + 2 * X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 * X + 3 * X ^ 2 + 2 * X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
  rw [hp]
  apply goodJets_of_coefficients _ ![4, 4, 0, 0, 0, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (16, 1).
private theorem row_16_1 : PairCertificate ![0, 0, 0, 0, 1] ![1, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 0, 0, 1] ![1, 0] =
    ![X ^ 7,
      1 + X + X ^ 3 + X ^ 7,
      1 + X + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 8,
      X + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      1 + X + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 * X + 3 * X ^ 2 + 2 * X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + 3 * X ^ 2 + 2 * X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
  rw [hp]
  apply goodJets_of_coefficients _ ![7, 0, 0, 1, 0, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (16, 2).
private theorem row_16_2 : PairCertificate ![0, 0, 0, 0, 1] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 0, 0, 1] ![0, 1] =
    ![X ^ 4 + X ^ 5 + X ^ 8,
      X + X ^ 2 + X ^ 5 + X ^ 8,
      1 + X + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X ^ 2 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 * X + 4 * X ^ 2 + 3 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 3 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![4, 1, 0, 2, 0, 1]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (16, 3).
private theorem row_16_3 : PairCertificate ![0, 0, 0, 0, 1] ![1, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 0, 0, 1] ![1, 1] =
    ![X ^ 5 + X ^ 7 + X ^ 8,
      1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 7 + X ^ 8,
      1 + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      1 + X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      1 + X + X ^ 2 + X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9,
      X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (3 * X + 4 * X ^ 2 + 3 * X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 3 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2 + X ^ 5 + X ^ 6) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![5, 0, 0, 0, 0, 3]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (17, 0).
private theorem row_17_0 : PairCertificate ![1, 0, 0, 0, 1] ![0, 0] := by
  intro _
  have hp : sixJetPolynomials ![1, 0, 0, 0, 1] ![0, 0] =
    ![1 + X ^ 4,
      1 + X ^ 4,
      X ^ 4,
      X ^ 4,
      1 + X ^ 4,
      1 + X ^ 4] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + 3 * X ^ 2 + 2 * X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 2 * X + 3 * X ^ 2 + 2 * X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 0, 4, 4, 0, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (17, 1).
private theorem row_17_1 : PairCertificate ![1, 0, 0, 0, 1] ![1, 0] := by
  intro h
  have hf : (1 + X + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 0, 0, 0, 1]) (ordinate ![1, 0]) := by
    refine ⟨X + X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - X ^ 3 - X ^ 5 - X ^ 7) * two_poly
  exact False.elim (obstruction_67 (hf.trans h))

-- Coefficient bit codes (a, b) = (17, 2).
private theorem row_17_2 : PairCertificate ![1, 0, 0, 0, 1] ![0, 1] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 0, 0, 0, 1]) (ordinate ![0, 1]) := by
    refine ⟨1 + X, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - X ^ 3 - X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_109 (hf.trans h))

-- Coefficient bit codes (a, b) = (17, 3).
private theorem row_17_3 : PairCertificate ![1, 0, 0, 0, 1] ![1, 1] := by
  intro _
  have hp : sixJetPolynomials ![1, 0, 0, 0, 1] ![1, 1] =
    ![1 + X ^ 5 + X ^ 7 + X ^ 8,
      X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 7 + X ^ 8,
      X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 4 * X ^ 2 + 3 * X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 3 * X + 3 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 2, 2, 1, 0, 3]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (18, 0).
private theorem row_18_0 : PairCertificate ![0, 1, 0, 0, 1] ![0, 0] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 4 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 1, 0, 0, 1]) (ordinate ![0, 0]) := by
    refine ⟨X ^ 2 + X ^ 4, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X ^ 4 + X ^ 5 - X ^ 6) * two_poly
  exact False.elim (obstruction_21 (hf.trans h))

-- Coefficient bit codes (a, b) = (18, 1).
private theorem row_18_1 : PairCertificate ![0, 1, 0, 0, 1] ![1, 0] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 1, 0, 0, 1]) (ordinate ![1, 0]) := by
    refine ⟨X + X ^ 3, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 3 - 2 * X ^ 4 - X ^ 5 - X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_61 (hf.trans h))

-- Coefficient bit codes (a, b) = (18, 2).
private theorem row_18_2 : PairCertificate ![0, 1, 0, 0, 1] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 0, 0, 1] ![0, 1] =
    ![X + X ^ 4 + X ^ 5 + X ^ 8,
      X ^ 2 + X ^ 5 + X ^ 8,
      X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X + X ^ 2 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 4 * X ^ 2 + 3 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 3 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 2, 4, 0, 0, 1]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (18, 3).
private theorem row_18_3 : PairCertificate ![0, 1, 0, 0, 1] ![1, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 0, 0, 1] ![1, 1] =
    ![X + X ^ 5 + X ^ 7 + X ^ 8,
      1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 7 + X ^ 8,
      X + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      1 + X + X ^ 2 + X ^ 7 + X ^ 8 + X ^ 9,
      X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 4 * X ^ 2 + 3 * X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 4 * X + 3 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 0, 1, 2, 0, 4]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (19, 0).
private theorem row_19_0 : PairCertificate ![1, 1, 0, 0, 1] ![0, 0] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 8 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 0, 0, 1]) (ordinate ![0, 0]) := by
    refine ⟨1, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (X + X ^ 4 + X ^ 5) * two_poly
  exact False.elim (obstruction_261 (hf.trans h))

-- Coefficient bit codes (a, b) = (19, 1).
private theorem row_19_1 : PairCertificate ![1, 1, 0, 0, 1] ![1, 0] := by
  intro _
  have hp : sixJetPolynomials ![1, 1, 0, 0, 1] ![1, 0] =
    ![1 + X + X ^ 7,
      X ^ 3 + X ^ 7,
      1 + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 8,
      X ^ 5 + X ^ 6 + X ^ 8,
      1 + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      1 + X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 3 * X ^ 2 + 2 * X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 3 * X + 3 * X ^ 2 + 2 * X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 3) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 3, 0, 5, 0, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (19, 2).
private theorem row_19_2 : PairCertificate ![1, 1, 0, 0, 1] ![0, 1] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 0, 0, 1]) (ordinate ![0, 1]) := by
    refine ⟨1 + X, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X ^ 2 - X ^ 3 - X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_117 (hf.trans h))

-- Coefficient bit codes (a, b) = (19, 3).
private theorem row_19_3 : PairCertificate ![1, 1, 0, 0, 1] ![1, 1] := by
  intro _
  have hp : sixJetPolynomials ![1, 1, 0, 0, 1] ![1, 1] =
    ![1 + X + X ^ 5 + X ^ 7 + X ^ 8,
      X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 7 + X ^ 8,
      1 + X + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      1 + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      1 + X + X ^ 2 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X ^ 7 + X ^ 8 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 4 * X ^ 2 + 3 * X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 4 * X + 3 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 1, 0, 0, 0, 7]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (20, 0).
private theorem row_20_0 : PairCertificate ![0, 0, 1, 0, 1] ![0, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 1, 0, 1] ![0, 0] =
    ![X ^ 2 + X ^ 4,
      X ^ 2 + X ^ 4,
      X ^ 2 + X ^ 4,
      X ^ 2 + X ^ 4,
      1 + X ^ 2,
      1 + X ^ 2] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 3 * X ^ 2 + 2 * X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 3 * X ^ 2 + 2 * X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
  rw [hp]
  apply goodJets_of_coefficients _ ![2, 2, 2, 2, 0, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (20, 1).
private theorem row_20_1 : PairCertificate ![0, 0, 1, 0, 1] ![1, 0] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 5 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 0, 1, 0, 1]) (ordinate ![1, 0]) := by
    refine ⟨X ^ 2 + X ^ 3, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X ^ 2 - X ^ 3 - X ^ 4 - 2 * X ^ 5 + X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_37 (hf.trans h))

-- Coefficient bit codes (a, b) = (20, 2).
private theorem row_20_2 : PairCertificate ![0, 0, 1, 0, 1] ![0, 1] := by
  intro h
  have hf : (1 + X + X ^ 3 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 0, 1, 0, 1]) (ordinate ![0, 1]) := by
    refine ⟨X ^ 3 + X ^ 4, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X ^ 3 - X ^ 4 - X ^ 5 - X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_11 (hf.trans h))

-- Coefficient bit codes (a, b) = (20, 3).
private theorem row_20_3 : PairCertificate ![0, 0, 1, 0, 1] ![1, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 1, 0, 1] ![1, 1] =
    ![X ^ 2 + X ^ 5 + X ^ 7 + X ^ 8,
      1 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 7 + X ^ 8,
      X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      1 + X + X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9,
      X ^ 2 + X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 4 * X + 5 * X ^ 2 + 3 * X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 4 * X + 4 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2 + X ^ 5 + X ^ 6) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![2, 0, 3, 1, 0, 2]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (21, 0).
private theorem row_21_0 : PairCertificate ![1, 0, 1, 0, 1] ![0, 0] := by
  intro h
  have hf : (1 + X ^ 4 + X ^ 8 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 0, 1, 0, 1]) (ordinate ![0, 0]) := by
    refine ⟨1, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (X ^ 2 + X ^ 4 + X ^ 6) * two_poly
  exact False.elim (obstruction_273 (hf.trans h))

-- Coefficient bit codes (a, b) = (21, 1).
private theorem row_21_1 : PairCertificate ![1, 0, 1, 0, 1] ![1, 0] := by
  intro h
  have hf : (1 + X ^ 3 + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 0, 1, 0, 1]) (ordinate ![1, 0]) := by
    refine ⟨X + X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 3 - 2 * X ^ 5 + X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_73 (hf.trans h))

-- Coefficient bit codes (a, b) = (21, 2).
private theorem row_21_2 : PairCertificate ![1, 0, 1, 0, 1] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![1, 0, 1, 0, 1] ![0, 1] =
    ![1 + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 8,
      1 + X + X ^ 5 + X ^ 8,
      1 + X + X ^ 2 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X ^ 7 + X ^ 8 + X ^ 9,
      1 + X + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 8,
      X + X ^ 5 + X ^ 6 + X ^ 8] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 4 * X ^ 2 + 3 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 4 * X + 4 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X ^ 2 + X ^ 4) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 0, 0, 7, 0, 1]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (21, 3).
private theorem row_21_3 : PairCertificate ![1, 0, 1, 0, 1] ![1, 1] := by
  intro h
  have hf : (1 + X + X ^ 3 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 0, 1, 0, 1]) (ordinate ![1, 1]) := by
    refine ⟨X ^ 3, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - 2 * X ^ 3 - X ^ 4 - 3 * X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_11 (hf.trans h))

-- Coefficient bit codes (a, b) = (22, 0).
private theorem row_22_0 : PairCertificate ![0, 1, 1, 0, 1] ![0, 0] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 1, 1, 0, 1]) (ordinate ![0, 0]) := by
    refine ⟨X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (X ^ 3 + X ^ 5 + X ^ 6) * two_poly
  exact False.elim (obstruction_69 (hf.trans h))

-- Coefficient bit codes (a, b) = (22, 1).
private theorem row_22_1 : PairCertificate ![0, 1, 1, 0, 1] ![1, 0] := by
  intro h
  have hf : (1 + X + X ^ 3 + X ^ 4 + X ^ 5 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 1, 1, 0, 1]) (ordinate ![1, 0]) := by
    refine ⟨X + X ^ 3, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - 2 * X ^ 4 - X ^ 5 - X ^ 7) * two_poly
  exact False.elim (obstruction_59 (hf.trans h))

-- Coefficient bit codes (a, b) = (22, 2).
private theorem row_22_2 : PairCertificate ![0, 1, 1, 0, 1] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 1, 0, 1] ![0, 1] =
    ![X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 8,
      X ^ 5 + X ^ 8,
      1 + X ^ 2 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 4 * X + 4 * X ^ 2 + 3 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 4 * X + 4 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X ^ 2) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 5, 0, 1, 0, 1]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (22, 3).
private theorem row_22_3 : PairCertificate ![0, 1, 1, 0, 1] ![1, 1] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 1, 1, 0, 1]) (ordinate ![1, 1]) := by
    refine ⟨X, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - X ^ 3 - 2 * X ^ 4 - 3 * X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_61 (hf.trans h))

-- Coefficient bit codes (a, b) = (23, 0).
private theorem row_23_0 : PairCertificate ![1, 1, 1, 0, 1] ![0, 0] := by
  intro h
  have hf : (1 + X ^ 4 + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 1, 0, 1]) (ordinate ![0, 0]) := by
    refine ⟨1 + X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5) * two_poly
  exact False.elim (obstruction_81 (hf.trans h))

-- Coefficient bit codes (a, b) = (23, 1).
private theorem row_23_1 : PairCertificate ![1, 1, 1, 0, 1] ![1, 0] := by
  intro h
  have hf : (1 + X + X ^ 3 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 1, 0, 1]) (ordinate ![1, 0]) := by
    refine ⟨X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X ^ 3 - X ^ 4 - 2 * X ^ 5 - X ^ 7) * two_poly
  exact False.elim (obstruction_11 (hf.trans h))

-- Coefficient bit codes (a, b) = (23, 2).
private theorem row_23_2 : PairCertificate ![1, 1, 1, 0, 1] ![0, 1] := by
  intro h
  have hf : (1 + X + X ^ 3 + X ^ 4 + X ^ 5 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 1, 0, 1]) (ordinate ![0, 1]) := by
    refine ⟨1 + X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X ^ 3 - X ^ 5 - X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_59 (hf.trans h))

-- Coefficient bit codes (a, b) = (23, 3).
private theorem row_23_3 : PairCertificate ![1, 1, 1, 0, 1] ![1, 1] := by
  intro _
  have hp : sixJetPolynomials ![1, 1, 1, 0, 1] ![1, 1] =
    ![1 + X + X ^ 2 + X ^ 5 + X ^ 7 + X ^ 8,
      X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 7 + X ^ 8,
      X + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      1 + X + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X ^ 2 + X ^ 7 + X ^ 8 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 4 * X + 5 * X ^ 2 + 3 * X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (3 + 5 * X + 4 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 1, 1, 4, 0, 2]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (24, 0).
private theorem row_24_0 : PairCertificate ![0, 0, 0, 1, 1] ![0, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 0, 1, 1] ![0, 0] =
    ![X ^ 3 + X ^ 4,
      X ^ 3 + X ^ 4,
      X + X ^ 2 + X ^ 3 + X ^ 4,
      X + X ^ 2 + X ^ 3 + X ^ 4,
      1 + X,
      1 + X] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 4 * X ^ 2 + 2 * X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 3 * X + 4 * X ^ 2 + 2 * X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
  rw [hp]
  apply goodJets_of_coefficients _ ![3, 3, 1, 1, 0, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (24, 1).
private theorem row_24_1 : PairCertificate ![0, 0, 0, 1, 1] ![1, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 0, 1, 1] ![1, 0] =
    ![X ^ 3 + X ^ 7,
      1 + X + X ^ 7,
      X ^ 5 + X ^ 6 + X ^ 8,
      1 + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      1 + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 4 * X + 5 * X ^ 2 + 3 * X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 4 * X + 4 * X ^ 2 + 2 * X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![3, 0, 5, 0, 0, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (24, 2).
private theorem row_24_2 : PairCertificate ![0, 0, 0, 1, 1] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 0, 1, 1] ![0, 1] =
    ![X ^ 3 + X ^ 4 + X ^ 5 + X ^ 8,
      X + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 8,
      X ^ 2 + X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X + X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 4 * X + 5 * X ^ 2 + 3 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 4 * X + 5 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![3, 1, 2, 0, 0, 2]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (24, 3).
private theorem row_24_3 : PairCertificate ![0, 0, 0, 1, 1] ![1, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 0, 1, 1] ![1, 1] =
    ![X ^ 3 + X ^ 5 + X ^ 7 + X ^ 8,
      1 + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 7 + X ^ 8,
      X + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      1 + X ^ 2 + X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9,
      X + X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 4 * X + 6 * X ^ 2 + 4 * X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 5 * X + 5 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2 + X ^ 5 + X ^ 6) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![3, 0, 1, 3, 0, 1]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (25, 0).
private theorem row_25_0 : PairCertificate ![1, 0, 0, 1, 1] ![0, 0] := by
  intro h
  have hf : (1 + X ^ 6 + X ^ 8 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 0, 0, 1, 1]) (ordinate ![0, 0]) := by
    refine ⟨1, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (X ^ 3 + X ^ 4 + X ^ 7) * two_poly
  exact False.elim (obstruction_321 (hf.trans h))

-- Coefficient bit codes (a, b) = (25, 1).
private theorem row_25_1 : PairCertificate ![1, 0, 0, 1, 1] ![1, 0] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 0, 0, 1, 1]) (ordinate ![1, 0]) := by
    refine ⟨X + X ^ 3, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 3 - X ^ 4 - 2 * X ^ 5 - X ^ 6) * two_poly
  exact False.elim (obstruction_61 (hf.trans h))

-- Coefficient bit codes (a, b) = (25, 2).
private theorem row_25_2 : PairCertificate ![1, 0, 0, 1, 1] ![0, 1] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 0, 0, 1, 1]) (ordinate ![0, 1]) := by
    refine ⟨1 + X, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - X ^ 4 - 2 * X ^ 5 - X ^ 6) * two_poly
  exact False.elim (obstruction_61 (hf.trans h))

-- Coefficient bit codes (a, b) = (25, 3).
private theorem row_25_3 : PairCertificate ![1, 0, 0, 1, 1] ![1, 1] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 5 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 0, 0, 1, 1]) (ordinate ![1, 1]) := by
    refine ⟨X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - 2 * X ^ 4 - 3 * X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_37 (hf.trans h))

-- Coefficient bit codes (a, b) = (26, 0).
private theorem row_26_0 : PairCertificate ![0, 1, 0, 1, 1] ![0, 0] := by
  intro h
  have hf : (1 + X ^ 4 + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 1, 0, 1, 1]) (ordinate ![0, 0]) := by
    refine ⟨X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (X ^ 4 + X ^ 5 + X ^ 7) * two_poly
  exact False.elim (obstruction_81 (hf.trans h))

-- Coefficient bit codes (a, b) = (26, 1).
private theorem row_26_1 : PairCertificate ![0, 1, 0, 1, 1] ![1, 0] := by
  intro h
  have hf : (1 + X + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 1, 0, 1, 1]) (ordinate ![1, 0]) := by
    refine ⟨X + X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - X ^ 3 - X ^ 4) * two_poly
  exact False.elim (obstruction_67 (hf.trans h))

-- Coefficient bit codes (a, b) = (26, 2).
private theorem row_26_2 : PairCertificate ![0, 1, 0, 1, 1] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 0, 1, 1] ![0, 1] =
    ![X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 8,
      X ^ 2 + X ^ 3 + X ^ 5 + X ^ 8,
      1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 4 * X + 5 * X ^ 2 + 3 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 5 * X + 5 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 2, 0, 3, 0, 2]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (26, 3).
private theorem row_26_3 : PairCertificate ![0, 1, 0, 1, 1] ![1, 1] := by
  intro h
  have hf : (1 + X + X ^ 3 + X ^ 4 + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 1, 0, 1, 1]) (ordinate ![1, 1]) := by
    refine ⟨X, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - X ^ 3 - 2 * X ^ 4 - 3 * X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_91 (hf.trans h))

-- Coefficient bit codes (a, b) = (27, 0).
private theorem row_27_0 : PairCertificate ![1, 1, 0, 1, 1] ![0, 0] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 4 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 0, 1, 1]) (ordinate ![0, 0]) := by
    refine ⟨1 + X ^ 4, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 7) * two_poly
  exact False.elim (obstruction_21 (hf.trans h))

-- Coefficient bit codes (a, b) = (27, 1).
private theorem row_27_1 : PairCertificate ![1, 1, 0, 1, 1] ![1, 0] := by
  intro _
  have hp : sixJetPolynomials ![1, 1, 0, 1, 1] ![1, 0] =
    ![1 + X + X ^ 3 + X ^ 7,
      X ^ 7,
      X + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 8,
      1 + X + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      1 + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 4 * X + 5 * X ^ 2 + 3 * X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 4 * X + 4 * X ^ 2 + 2 * X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 3) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 7, 1, 0, 0, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (27, 2).
private theorem row_27_2 : PairCertificate ![1, 1, 0, 1, 1] ![0, 1] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 5 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 0, 1, 1]) (ordinate ![0, 1]) := by
    refine ⟨1 + X, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X ^ 2 + X ^ 4 - X ^ 5 - X ^ 6) * two_poly
  exact False.elim (obstruction_37 (hf.trans h))

-- Coefficient bit codes (a, b) = (27, 3).
private theorem row_27_3 : PairCertificate ![1, 1, 0, 1, 1] ![1, 1] := by
  intro _
  have hp : sixJetPolynomials ![1, 1, 0, 1, 1] ![1, 1] =
    ![1 + X + X ^ 3 + X ^ 5 + X ^ 7 + X ^ 8,
      X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 7 + X ^ 8,
      X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      1 + X ^ 2 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X + X ^ 7 + X ^ 8 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 5 * X + 6 * X ^ 2 + 4 * X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (3 + 5 * X + 5 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 1, 5, 1, 0, 1]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (28, 0).
private theorem row_28_0 : PairCertificate ![0, 0, 1, 1, 1] ![0, 0] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 4 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 0, 1, 1, 1]) (ordinate ![0, 0]) := by
    refine ⟨X ^ 4, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (X ^ 5 + X ^ 6 + X ^ 7) * two_poly
  exact False.elim (obstruction_21 (hf.trans h))

-- Coefficient bit codes (a, b) = (28, 1).
private theorem row_28_1 : PairCertificate ![0, 0, 1, 1, 1] ![1, 0] := by
  intro h
  have hf : (1 + X + X ^ 3 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 0, 1, 1, 1]) (ordinate ![1, 0]) := by
    refine ⟨X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4 - 2 * X ^ 5) * two_poly
  exact False.elim (obstruction_11 (hf.trans h))

-- Coefficient bit codes (a, b) = (28, 2).
private theorem row_28_2 : PairCertificate ![0, 0, 1, 1, 1] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 0, 1, 1, 1] ![0, 1] =
    ![X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 8,
      X + X ^ 3 + X ^ 5 + X ^ 8,
      1 + X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X + X ^ 2 + X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + 5 * X + 6 * X ^ 2 + 3 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 5 * X + 5 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![2, 1, 0, 1, 0, 4]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (28, 3).
private theorem row_28_3 : PairCertificate ![0, 0, 1, 1, 1] ![1, 1] := by
  intro h
  have hf : (1 + X + X ^ 3 + X ^ 4 + X ^ 5 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 0, 1, 1, 1]) (ordinate ![1, 1]) := by
    refine ⟨X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4 - 3 * X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_59 (hf.trans h))

-- Coefficient bit codes (a, b) = (29, 0).
private theorem row_29_0 : PairCertificate ![1, 0, 1, 1, 1] ![0, 0] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 0, 1, 1, 1]) (ordinate ![0, 0]) := by
    refine ⟨1 + X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7) * two_poly
  exact False.elim (obstruction_69 (hf.trans h))

-- Coefficient bit codes (a, b) = (29, 1).
private theorem row_29_1 : PairCertificate ![1, 0, 1, 1, 1] ![1, 0] := by
  intro h
  have hf : (1 + X + X ^ 3 + X ^ 4 + X ^ 5 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 0, 1, 1, 1]) (ordinate ![1, 0]) := by
    refine ⟨X + X ^ 3, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 3 - X ^ 4 - X ^ 5) * two_poly
  exact False.elim (obstruction_59 (hf.trans h))

-- Coefficient bit codes (a, b) = (29, 2).
private theorem row_29_2 : PairCertificate ![1, 0, 1, 1, 1] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![1, 0, 1, 1, 1] ![0, 1] =
    ![1 + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 8,
      1 + X + X ^ 3 + X ^ 5 + X ^ 8,
      X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X + X ^ 2 + X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 6 + X ^ 8,
      X ^ 5 + X ^ 6 + X ^ 8] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 2 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 5 * X + 6 * X ^ 2 + 3 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 5 * X + 5 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2 + X ^ 4) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 0, 3, 0, 0, 5]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (29, 3).
private theorem row_29_3 : PairCertificate ![1, 0, 1, 1, 1] ![1, 1] := by
  intro _
  have hp : sixJetPolynomials ![1, 0, 1, 1, 1] ![1, 1] =
    ![1 + X ^ 2 + X ^ 3 + X ^ 5 + X ^ 7 + X ^ 8,
      X ^ 4 + X ^ 5 + X ^ 7 + X ^ 8,
      X + X ^ 2 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 9,
      1 + X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      X + X ^ 2 + X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2 + X ^ 3 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 5 * X + 6 * X ^ 2 + 4 * X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (3 + 6 * X + 5 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![0, 4, 1, 2, 0, 1]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (30, 0).
private theorem row_30_0 : PairCertificate ![0, 1, 1, 1, 1] ![0, 0] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 1, 1, 1] ![0, 0] =
    ![X + X ^ 2 + X ^ 3 + X ^ 4,
      X + X ^ 2 + X ^ 3 + X ^ 4,
      X ^ 3 + X ^ 4,
      X ^ 3 + X ^ 4,
      1 + X + X ^ 2 + X ^ 3,
      1 + X + X ^ 2 + X ^ 3] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 5 * X + 5 * X ^ 2 + 2 * X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 5 * X + 5 * X ^ 2 + 2 * X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 1, 3, 3, 0, 0]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (30, 1).
private theorem row_30_1 : PairCertificate ![0, 1, 1, 1, 1] ![1, 0] := by
  intro h
  have hf : (1 + X ^ 3 + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 1, 1, 1, 1]) (ordinate ![1, 0]) := by
    refine ⟨X + X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - X ^ 4 + X ^ 6) * two_poly
  exact False.elim (obstruction_73 (hf.trans h))

-- Coefficient bit codes (a, b) = (30, 2).
private theorem row_30_2 : PairCertificate ![0, 1, 1, 1, 1] ![0, 1] := by
  intro _
  have hp : sixJetPolynomials ![0, 1, 1, 1, 1] ![0, 1] =
    ![X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 8,
      X ^ 3 + X ^ 5 + X ^ 8,
      X + X ^ 3 + X ^ 4 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X ^ 2 + X ^ 3 + X ^ 7 + X ^ 8 + X ^ 9,
      1 + X ^ 2 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8,
      X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 8] := by
    funext i
    fin_cases i
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        ring
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 2 + X ^ 4) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 5 * X + 6 * X ^ 2 + 3 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (2 + 6 * X + 5 * X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (X + X ^ 3) * two_poly
    · norm_num [sixJetPolynomials, numerator, ordinate, infinityNumerator,
        infinityOrdinate, jetZeroZero, jetZeroOne, jetOneZero, jetOneOne,
        jetInfinityZero, jetInfinityOne, Fin.sum_univ_succ,
        Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp] <;>
        linear_combination (1 + X + X ^ 2) * two_poly
  rw [hp]
  apply goodJets_of_coefficients _ ![1, 3, 1, 0, 0, 3]
  · decide
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X]
  · intro i j hj
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X] at *
  · decide

-- Coefficient bit codes (a, b) = (30, 3).
private theorem row_30_3 : PairCertificate ![0, 1, 1, 1, 1] ![1, 1] := by
  intro h
  have hf : (1 + X + X ^ 3 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![0, 1, 1, 1, 1]) (ordinate ![1, 1]) := by
    refine ⟨X + X ^ 2 + X ^ 3 + X ^ 4, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - 2 * X ^ 2 - 2 * X ^ 3 - 3 * X ^ 4 - 3 * X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_11 (hf.trans h))

-- Coefficient bit codes (a, b) = (31, 0).
private theorem row_31_0 : PairCertificate ![1, 1, 1, 1, 1] ![0, 0] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 4 + X ^ 6 + X ^ 8 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 1, 1, 1]) (ordinate ![0, 0]) := by
    refine ⟨1, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (X + X ^ 2 + 2 * X ^ 3 + 2 * X ^ 4 + 2 * X ^ 5 + X ^ 6 + X ^ 7) * two_poly
  exact False.elim (obstruction_341 (hf.trans h))

-- Coefficient bit codes (a, b) = (31, 1).
private theorem row_31_1 : PairCertificate ![1, 1, 1, 1, 1] ![1, 0] := by
  intro h
  have hf : (1 + X ^ 2 + X ^ 5 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 1, 1, 1]) (ordinate ![1, 0]) := by
    refine ⟨X ^ 2 + X ^ 3, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (X ^ 6) * two_poly
  exact False.elim (obstruction_37 (hf.trans h))

-- Coefficient bit codes (a, b) = (31, 2).
private theorem row_31_2 : PairCertificate ![1, 1, 1, 1, 1] ![0, 1] := by
  intro h
  have hf : (1 + X + X ^ 3 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 1, 1, 1]) (ordinate ![0, 1]) := by
    refine ⟨1 + X ^ 2, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (X ^ 4) * two_poly
  exact False.elim (obstruction_11 (hf.trans h))

-- Coefficient bit codes (a, b) = (31, 3).
private theorem row_31_3 : PairCertificate ![1, 1, 1, 1, 1] ![1, 1] := by
  intro h
  have hf : (1 + X + X ^ 2 + X ^ 5 + X ^ 6 : K[X]) ∣
      N13SpecialAffineNorm.normPolynomial (numerator ![1, 1, 1, 1, 1]) (ordinate ![1, 1]) := by
    refine ⟨X, ?_⟩
    norm_num [N13SpecialAffineNorm.normPolynomial, numerator, ordinate,
      N13GoodCoordinateRingTwo.hPoly, N13GoodCoordinateRingTwo.rhsPoly,
      Fin.sum_univ_succ] <;>
      linear_combination (-X - X ^ 2 - X ^ 3 - X ^ 4 - 2 * X ^ 5 - 2 * X ^ 6 - X ^ 7) * two_poly
  exact False.elim (obstruction_103 (hf.trans h))

private theorem binary (x : K) : x = 0 ∨ x = 1 := by
  revert x; decide

/-- The norm-support restriction leaves only genuine nonzero nine-jets,
and every surviving pair has zero weighted code. The common infinity
shift -4 cancels between the last two coefficients, whose weights sum to 0. -/
theorem supported_small_function_certificate :
    ∀ (a : Fin 5 → K) (b : Fin 2 → K),
      N13SpecialAffineNorm.normPolynomial (numerator a) (ordinate b) ∣
          (X : K[X]) ^ 16 * (X - 1) ^ 16 →
        (∀ i : Fin 6, sixJetOrders a b i < 9 ∧
          (sixJetPolynomials a b i).coeff (sixJetOrders a b i) ≠ 0 ∧
          ∀ j : Fin 9, (j : ℕ) < sixJetOrders a b i → (sixJetPolynomials a b i).coeff j = 0) ∧
        weightedJetCode a b = 0 := by
  intro a b
  change PairCertificate a b
  have ha : a = ![a 0, a 1, a 2, a 3, a 4] := by
    funext i
    fin_cases i <;> rfl
  have hb : b = ![b 0, b 1] := by
    funext i
    fin_cases i <;> rfl
  rw [ha, hb]
  rcases binary (a 0) with h0 | h0 <;>
    rcases binary (a 1) with h1 | h1 <;>
    rcases binary (a 2) with h2 | h2 <;>
    rcases binary (a 3) with h3 | h3 <;>
    rcases binary (a 4) with h4 | h4 <;>
    rcases binary (b 0) with k0 | k0 <;>
    rcases binary (b 1) with k1 | k1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_0_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_0_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_0_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_0_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_16_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_16_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_16_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_16_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_8_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_8_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_8_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_8_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_24_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_24_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_24_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_24_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_4_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_4_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_4_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_4_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_20_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_20_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_20_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_20_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_12_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_12_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_12_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_12_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_28_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_28_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_28_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_28_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_2_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_2_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_2_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_2_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_18_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_18_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_18_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_18_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_10_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_10_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_10_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_10_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_26_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_26_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_26_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_26_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_6_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_6_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_6_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_6_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_22_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_22_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_22_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_22_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_14_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_14_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_14_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_14_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_30_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_30_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_30_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_30_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_1_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_1_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_1_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_1_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_17_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_17_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_17_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_17_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_9_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_9_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_9_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_9_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_25_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_25_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_25_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_25_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_5_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_5_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_5_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_5_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_21_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_21_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_21_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_21_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_13_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_13_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_13_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_13_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_29_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_29_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_29_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_29_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_3_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_3_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_3_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_3_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_19_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_19_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_19_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_19_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_11_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_11_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_11_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_11_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_27_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_27_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_27_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_27_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_7_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_7_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_7_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_7_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_23_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_23_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_23_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_23_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_15_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_15_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_15_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_15_3
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_31_0
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_31_2
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_31_1
  · simpa only [h0, h1, h2, h3, h4, k0, k1] using row_31_3

end
end MazurProof.N13SpecialSmallFunctionCertificate
