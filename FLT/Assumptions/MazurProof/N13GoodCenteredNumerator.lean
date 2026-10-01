import FLT.Assumptions.MazurProof.N13CenteredNumeratorPoleBounds

/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

Change the actual small principal numerator from the sextic coordinates to
the good model. Its membership in the SAME fixed base ideal forces the
polynomial part to be divisible by uBase. Thus the regular numerator has
the exact Hermite shape uBase*A+b*y, with deg A≤2 and deg b≤1 over Q2.
-/

namespace MazurProof.N13GoodCenteredNumerator

noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev Good := N13GoodSexticCoordinateEquiv.GoodRing (K := K)
abbrev toGood := N13GoodSexticCoordinateEquiv.toGood (K := K)
abbrev toSextic := N13GoodSexticCoordinateEquiv.toSextic (K := K)
abbrev gx := N13GeneralizedMumfordIntegral.xClass (R := K)
abbrev gy := N13GeneralizedMumfordIntegral.yClass (R := K)

def goodP (n : R) : K[X] := coeff0 M n + coeffY M n * N13GeneralizedMumfordIntegral.hPoly
def goodQ (n : R) : K[X] := 2 * coeffY M n

theorem toGood_recompose (n : R) :
    toGood n = gx (goodP n) + gx (goodQ n) * gy := by
  rw [← recompose M n, map_add, map_mul,
    N13GoodSexticCoordinateEquiv.toGood_xClass,
    N13GoodSexticCoordinateEquiv.toGood_xClass,
    N13GoodSexticCoordinateEquiv.toGood_yClass]
  simp only [goodP, goodQ, N13GoodSexticCoordinateEquiv.sexticYInGood,
    N13GoodSexticCoordinateEquiv.goodXHom_apply,
    N13GeneralizedMumfordIntegral.xClass_add,
    N13GeneralizedMumfordIntegral.xClass_mul,
    N13GeneralizedMumfordIntegral.xClass_natCast]
  ring

theorem toGood_mumfordIdeal (P : DiskPair) :
    Ideal.map toGood (mumfordIdeal M P.mumford.u P.mumford.v) =
      N13GeneralizedMumfordIntegral.mumfordIdeal
        (N13TwoAdicMumfordTransport.mapPoly P.u)
        (N13TwoAdicMumfordTransport.mapPoly P.v) := by
  have ht := N13TwoAdicMumfordTransport.map_mumfordIdeal_sexticSemi P.smoothMumford 0
  change Ideal.map toSextic
    (N13GeneralizedMumfordIntegral.mumfordIdeal
      (N13TwoAdicMumfordTransport.mapPoly P.u)
      (N13TwoAdicMumfordTransport.mapPoly P.v)) =
        mumfordIdeal M P.mumford.u P.mumford.v at ht
  have hi : toGood.comp toSextic = RingHom.id Good := by
    ext z
    exact (N13GoodSexticCoordinateEquiv.coordinateRingEquiv (K := K)).symm_apply_apply z
  rw [← ht, Ideal.map_map, hi, Ideal.map_id]

theorem base_divides_goodP (n : R)
    (hn : n ∈ mumfordIdeal M B.mumford.u B.mumford.v) :
    (X ^ 2 + X : K[X]) ∣ goodP n := by
  let D := N13TwoAdicMumfordTransport.baseChange B.smoothMumford
  have hu : D.u = X ^ 2 + X := by
    simp [D, N13TwoAdicMumfordTransport.mapPoly, N13FormalAbelLinearization.uBase]
  have hv : D.v = 0 := by simp [D]
  have hm := Ideal.mem_map_of_mem toGood hn
  rw [toGood_mumfordIdeal] at hm
  change toGood n ∈ N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v at hm
  have hd := (N13GeneralizedMumfordIntegral.mem_mumfordIdeal_iff D (toGood n)).mp hm
  rw [hu, hv, mul_zero, add_zero, toGood_recompose] at hd
  simpa only [map_add, N13GeneralizedMumfordIntegral.coeff0_xClass,
    N13GeneralizedMumfordIntegral.coeff0_xClass_mul_yClass, add_zero] using hd

theorem good_degrees (n : R)
    (hp : (coeff0 M n).natDegree ≤ 4) (hq : (coeffY M n).natDegree ≤ 1) :
    (goodP n).natDegree ≤ 4 ∧ (goodQ n).natDegree ≤ 1 := by
  have hh : (N13GeneralizedMumfordIntegral.hPoly (R := K)).natDegree ≤ 3 := by
    unfold N13GeneralizedMumfordIntegral.hPoly
    compute_degree!
  constructor
  · apply (natDegree_add_le _ _).trans
    apply max_le hp
    exact (natDegree_mul_le _ _).trans (by omega)
  · change ((2 : K[X]) * coeffY M n).natDegree ≤ 1
    have he := natDegree_mul_le (2 : K[X]) (coeffY M n)
    simpa using he.trans (by simpa using hq)

theorem exists_good_hermite_shape (n : R)
    (hp : (coeff0 M n).natDegree ≤ 4) (hq : (coeffY M n).natDegree ≤ 1)
    (hbase : n ∈ mumfordIdeal M B.mumford.u B.mumford.v) :
    ∃ A b : K[X], A.natDegree ≤ 2 ∧ b.natDegree ≤ 1 ∧
      toGood n = gx ((X ^ 2 + X) * A) + gx b * gy := by
  obtain ⟨A, hA⟩ := base_divides_goodP n hbase
  have hg := good_degrees n hp hq
  refine ⟨A, goodQ n, ?_, hg.2, ?_⟩
  · by_cases hz : A = 0
    · simp [hz]
    · have hU : (X ^ 2 + X : K[X]).Monic := by monicity!
      have hd : (X ^ 2 + X : K[X]).natDegree = 2 := by compute_degree!
      have hp' := hg.1
      rw [hA, natDegree_mul hU.ne_zero hz, hd] at hp'
      omega
  · rw [toGood_recompose, hA]

theorem selected_base_membership
    (P Q : DiskPair) (n : R)
    (hn : n ∈ (mumfordIdeal M Q.mumford.u Q.mumford.v *
        mumfordIdeal M B.mumford.u B.mumford.v) *
      (mumfordIdeal M (conjugateSemiMumford M P.mumford.toSemi).u
        (conjugateSemiMumford M P.mumford.toSemi).v) ^ 2) :
    n ∈ mumfordIdeal M B.mumford.u B.mumford.v :=
  Ideal.mul_le_left (Ideal.mul_le_right hn)

/-- The selected family supplies the exact small good-model shape with
the original nonzero numerator and product membership retained. -/
theorem exists_selected_good_shape
    {H : AddSubgroup N13RationalKernelDoublingAdapter.RationalPic}
    (L : N13RationalKernelDoublingAdapter.NearBaseFamily H) (z : H) :
    ∃ α : Fˣ, ∃ n : R, ∃ A b : K[X],
      n ≠ 0 ∧ A.natDegree ≤ 2 ∧ b.natDegree ≤ 1 ∧
      toGood n = gx ((X ^ 2 + X) * A) + gx b * gy ∧
      n ∈ (mumfordIdeal M (L.pair (2 • z)).mumford.u (L.pair (2 • z)).mumford.v *
          mumfordIdeal M B.mumford.u B.mumford.v) *
        (mumfordIdeal M (conjugateSemiMumford M (L.pair z).mumford.toSemi).u
          (conjugateSemiMumford M (L.pair z).mumford.toSemi).v) ^ 2 ∧
      algebraMap R F n = (α : F) * algebraMap R F (xClass M ((L.pair z).mumford.u ^ 2)) := by
  obtain ⟨α, n, hn, hp, hq, hmem, he⟩ :=
    N13CenteredNumeratorPoleBounds.exists_selected_small_numerator L z
  obtain ⟨A, b, hA, hb, hshape⟩ := exists_good_hermite_shape n hp hq
    (selected_base_membership (L.pair z) (L.pair (2 • z)) n hmem)
  exact ⟨α, n, A, b, hn, hA, hb, hshape, hmem, he⟩

end
end MazurProof.N13GoodCenteredNumerator
