import FLT.Assumptions.MazurProof.N13GoodCenteredNumerator
import FLT.Assumptions.MazurProof.N13GoodPointFirstJet
import FLT.Assumptions.MazurProof.N13HermiteResidualDivisibility

/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

Transport the actual conjugate graph through completion of the square and
evaluate its squared ideal in the actual opposite-sheet dual-number jets.
This proves the four Hermite equations for the SAME principal numerator
already extracted from the selected centered double.
-/

namespace MazurProof.N13ActualHermiteEquations

noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator N13GoodCenteredNumerator
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev c := N13TwoAdicMumfordTransport.coeffMap
def x (P : DiskPair) (j : Fin 2) : K := c (N13CenteredHermiteFirstOrder.x P j)
def y (P : DiskPair) (j : Fin 2) : K := c (N13CenteredHermiteFirstOrder.oppositeY P j)
def s (P : DiskPair) (j : Fin 2) : K := c (N13HermiteResidualDivisibility.slope P j)
def U (P : DiskPair) : K[X] := N13TwoAdicMumfordTransport.mapPoly P.u
def V (P : DiskPair) : K[X] :=
  -N13GeneralizedMumfordIntegral.hPoly - N13TwoAdicMumfordTransport.mapPoly P.v

theorem curve (P : DiskPair) (j : Fin 2) :
    y P j ^ 2 + (x P j ^ 3 + x P j + 1) * y P j -
      (x P j ^ 5 + x P j ^ 4) = 0 := by
  have h := congrArg c (N13HermiteResidualDivisibility.opposite_curve P j)
  simp only [map_sub, map_add, map_mul, map_pow, map_one, map_zero] at h
  change y P j ^ 2 + (x P j ^ 3 + x P j + 1) * y P j -
    (x P j ^ 2 + x P j) * x P j ^ 3 = 0 at h
  linear_combination h

theorem tangent (P : DiskPair) (j : Fin 2) :
    (2 * y P j + (x P j ^ 3 + x P j + 1)) * s P j +
      (3 * x P j ^ 2 + 1) * y P j - (5 * x P j ^ 4 + 4 * x P j ^ 3) = 0 := by
  have h := congrArg c (N13HermiteResidualDivisibility.slope_relation P j)
  simp only [map_sub, map_add, map_mul, map_pow, map_one, map_zero, map_ofNat] at h
  exact h

theorem U_root (P : DiskPair) (j : Fin 2) : (U P).eval (x P j) = 0 := by
  fin_cases j <;>
    simp [U, x, N13CenteredHermiteFirstOrder.x,
      N13TwoAdicMumfordTransport.mapPoly, Polynomial.eval_map_apply]

theorem V_eval (P : DiskPair) (j : Fin 2) : (V P).eval (x P j) = y P j := by
  fin_cases j <;>
    simp [V, x, y, N13CenteredHermiteFirstOrder.x,
      N13CenteredHermiteFirstOrder.oppositeY,
      N13TwoAdicMumfordTransport.mapPoly, Polynomial.eval_map_apply,
      N13GeneralizedMumfordIntegral.hPoly, N13GoodModelTwo.h]

theorem map_conjugate_graph (P : DiskPair) :
    Ideal.map toGood
      (mumfordIdeal M (conjugateSemiMumford M P.mumford.toSemi).u
        (conjugateSemiMumford M P.mumford.toSemi).v) =
      N13GeneralizedMumfordIntegral.mumfordIdeal (U P) (V P) := by
  let p := N13TwoAdicMumfordTransport.mapPoly P.v
  let W := N13GoodSexticMumfordTransport.completedGraph p
  have hmod : U P ∣ (-W) - (-(W % U P)) := by
    refine ⟨-(W / U P), ?_⟩
    have h := EuclideanDomain.mod_add_div W (U P)
    linear_combination h
  have ht : Ideal.map toSextic
      (N13GeneralizedMumfordIntegral.mumfordIdeal (U P) (V P)) =
        mumfordIdeal M (U P) (-(W % U P)) := by
    rw [N13GoodSexticMumfordTransport.map_mumfordIdeal]
    have hv : N13GoodSexticMumfordTransport.completedGraph (V P) = -W := by
      dsimp [V, W, p, N13GoodSexticMumfordTransport.completedGraph]
      ring
    rw [hv]
    exact N13GoodSexticMumfordTransport.sextic_mumfordIdeal_eq_of_dvd_sub _ _ _ hmod
  have hi : toGood.comp toSextic = RingHom.id Good := by
    exact RingHom.ext fun z =>
      (N13GoodSexticCoordinateEquiv.coordinateRingEquiv (K := K)).symm_apply_apply z
  change Ideal.map toGood (mumfordIdeal M (U P) (-(W % U P))) = _
  rw [← ht, Ideal.map_map, hi, Ideal.map_id]

theorem hermite_equations_of_product_membership
    (P Q : DiskPair) (n : R) (A b : K[X])
    (hshape : toGood n = gx ((X ^ 2 + X) * A) + gx b * gy)
    (hmem : n ∈ (mumfordIdeal M Q.mumford.u Q.mumford.v *
        mumfordIdeal M B.mumford.u B.mumford.v) *
      (mumfordIdeal M (conjugateSemiMumford M P.mumford.toSemi).u
        (conjugateSemiMumford M P.mumford.toSemi).v) ^ 2) :
    (∀ j, (x P j ^ 2 + x P j) * A.eval (x P j) + b.eval (x P j) * y P j = 0) ∧
      (∀ j, (2 * x P j + 1) * A.eval (x P j) +
        (x P j ^ 2 + x P j) * A.derivative.eval (x P j) +
        b.derivative.eval (x P j) * y P j + b.eval (x P j) * s P j = 0) := by
  have hn : n ∈ (mumfordIdeal M (conjugateSemiMumford M P.mumford.toSemi).u
      (conjugateSemiMumford M P.mumford.toSemi).v) ^ 2 := Ideal.mul_le_left hmem
  have hg := Ideal.mem_map_of_mem toGood hn
  rw [Ideal.map_pow, map_conjugate_graph, hshape] at hg
  have hj (j : Fin 2) := N13GoodPointFirstJet.value_derivative_of_square_graph
    (x P j) (y P j) (s P j) (curve P j) (tangent P j)
    (U P) (V P) ((X ^ 2 + X) * A) b (U_root P j) (V_eval P j) hg
  constructor
  · intro j
    simpa using (hj j).1
  · intro j
    have hd := (hj j).2
    simpa [derivative_mul, derivative_pow, add_assoc] using hd

end
end MazurProof.N13ActualHermiteEquations
