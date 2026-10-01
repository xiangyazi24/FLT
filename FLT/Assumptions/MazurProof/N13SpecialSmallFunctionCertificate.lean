import FLT.Assumptions.MazurProof.N13SpecialSmallNumerator

/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled B03 source candidate; all Lean and axiom checks NOT RUN.

Finite kernel-checkable polynomial certificates for the 32*4 coefficient
pairs supplied by the geometric small-numerator theorem. All arithmetic is
in the GOOD F2 model. These declarations use ordinary `decide`, never
native_decide. The identification of the nine-jet orders with the actual
six local orders is a separate geometric step, still to be assembled.
-/

namespace MazurProof.N13SpecialSmallFunctionCertificate

open Polynomial

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

/-- The displayed polynomials really satisfy all six local equations to
nine-jet precision. No analytic or numerical approximation is used. -/
set_option maxRecDepth 200000 in
theorem jet_polynomials_satisfy_equations :
    (X : K[X]) ^ 9 ∣ residual N13GoodCoordinateRingTwo.hPoly N13GoodCoordinateRingTwo.rhsPoly jetZeroZero ∧
    (X : K[X]) ^ 9 ∣ residual N13GoodCoordinateRingTwo.hPoly N13GoodCoordinateRingTwo.rhsPoly jetZeroOne ∧
    (X : K[X]) ^ 9 ∣ residual (N13GoodCoordinateRingTwo.hPoly.comp (X + 1))
      (N13GoodCoordinateRingTwo.rhsPoly.comp (X + 1)) jetOneZero ∧
    (X : K[X]) ^ 9 ∣ residual (N13GoodCoordinateRingTwo.hPoly.comp (X + 1))
      (N13GoodCoordinateRingTwo.rhsPoly.comp (X + 1)) jetOneOne ∧
    (X : K[X]) ^ 9 ∣ residual N13SpecialInfinityChart.hPoly N13SpecialInfinityChart.rhsPoly jetInfinityZero ∧
    (X : K[X]) ^ 9 ∣ residual N13SpecialInfinityChart.hPoly N13SpecialInfinityChart.rhsPoly jetInfinityOne := by
  decide

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

/-- The norm-support restriction leaves only genuine nonzero nine-jets,
and every surviving pair has zero weighted code. The common infinity
shift -4 cancels between the last two coefficients, whose weights sum to0. -/
set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem supported_small_function_certificate :
    ∀ (a : Fin 5 → K) (b : Fin 2 → K),
      N13SpecialAffineNorm.normPolynomial (numerator a) (ordinate b) ∣
          (X : K[X]) ^ 16 * (X - 1) ^ 16 →
        (∀ i : Fin 6, sixJetOrders a b i < 9 ∧
          (sixJetPolynomials a b i).coeff (sixJetOrders a b i) ≠ 0 ∧
          ∀ j : Fin 9, (j : ℕ) < sixJetOrders a b i → (sixJetPolynomials a b i).coeff j = 0) ∧
        weightedJetCode a b = 0 := by
  decide

end MazurProof.N13SpecialSmallFunctionCertificate
