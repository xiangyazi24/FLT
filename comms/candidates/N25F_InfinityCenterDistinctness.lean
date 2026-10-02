import FLT.Assumptions.MazurProof.N25F_InfinityParameterOrders
import FLT.Assumptions.MazurProof.N25F_InfinityBoundaryAlgebras
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.OrderOfVanishing.Basic

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityCenterDistinctness

/-- Equal centers give a common-field-compatible local equivalence. -/
theorem exists_equiv_of_same_center
    {A R S K : Type*} [CommRing A] [CommRing R] [CommRing S] [CommRing K]
    [Algebra A R] [Algebra A S]
    {p q : Ideal A} [p.IsPrime] [q.IsPrime]
    (eR : Localization.AtPrime p ≃ₐ[A] R)
    (eS : Localization.AtPrime q ≃ₐ[A] S)
    (gR : R →+* K) (gS : S →+* K)
    (hc : ∀ a, gR (algebraMap A R a) = gS (algebraMap A S a)) (hpq : p = q) :
    ∃ e : R ≃ₐ[A] S, ∀ r, gS (e r) = gR r := by
  subst q
  let e := eR.symm.trans eS
  refine ⟨e, ?_⟩
  have hm : gS.comp eS.toRingHom = gR.comp eR.toRingHom := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext a
    change gS (eS (algebraMap A (Localization.AtPrime p) a)) =
      gR (eR (algebraMap A (Localization.AtPrime p) a))
    rw [eS.commutes, eR.commutes]
    exact (hc a).symm
  intro r
  have hr := RingHom.congr_fun hm (eR.symm r)
  simpa [e] using hr

private theorem incompatible_unit_ratio
    {R S K : Type*} [CommRing R] [CommRing S] [Field K]
    (f : R →+* K) (g : S →+* K) (hf : Function.Injective f)
    (e : R ≃+* S) (he : ∀ r, g (e r) = f r)
    (a b : R) (v : S) (hv : IsUnit v)
    (hab : f a * g v = f b) (hord : Ring.ord R a ≠ Ring.ord R b) : False := by
  let u := e.symm v
  have hu : IsUnit u := hv.map e.symm.toRingHom
  have hfu : f u = g v := by simpa [u] using (he u).symm
  have hrel : a * u = b := by
    apply hf
    rw [map_mul, hfu]
    exact hab
  apply hord
  calc
    Ring.ord R a = Ring.ord R (a * u) := (Ring.ord_mul_of_isUnit_right hu a).symm
    _ = Ring.ord R b := congrArg (Ring.ord R) hrel


open N25F_InfinityNormalization N25F_InfinityBoundaryMaps
open N25F_InfinityBoundaryCenters N25F_InfinityLocalizations
open N25F_InfinityParameterOrders N25F_InfinityBoundaryAlgebras
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open N25F_XLocalFractionEmbedding N25F_YZLocalFractionEmbedding
open N25F_XCoordinateOrders N25F_XBoundaryZOrder N25F_XChartFractionMap
open N25F_YZLocalZUnit
local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
local notation "CurveField" => FractionRing W
attribute [local instance] infinityPolynomialAlgebra
  xInfinityBaseAlgebra yzInfinityBaseAlgebra zInfinityBaseAlgebra
  xInfinityNormalizationAlgebra yzInfinityNormalizationAlgebra zInfinityNormalizationAlgebra

private theorem xLocalToFraction_xYGerm :
    xLocalToFraction xYGerm = algebraMap W CurveField qy / algebraMap W CurveField qx := by
  rw [xYGerm, xLocalToFraction_algebraMap, xChartToFraction_xY]

/-- X and YZ have different centers: Z/Y is a unit at YZ, but its X-local
ratio has positive order, since ord(Y/X)=1 and ord(Z/X)=2. -/
theorem xInfinityPrime_ne_yzInfinityPrime : xInfinityPrime ≠ yzInfinityPrime := by
  intro hpq
  obtain ⟨e, he⟩ := exists_equiv_of_same_center
    xInfinityLocalizationEquiv yzInfinityLocalizationEquiv
    xLocalToFraction.toRingHom yzLocalToFraction.toRingHom
    (fun a => by
      change xLocalToFraction (infinityNormalizationToX a) =
        yzLocalToFraction (infinityNormalizationToYZ a)
      rw [xLocalToFraction_infinityNormalizationToX,
        yzLocalToFraction_infinityNormalizationToYZ]) hpq
  apply incompatible_unit_ratio xLocalToFraction.toRingHom yzLocalToFraction.toRingHom
    xLocalToFraction_injective e.toRingEquiv he
    xYGerm xZGerm yzZGerm yzZGerm_isUnit
  · change xLocalToFraction xYGerm * yzLocalToFraction yzZGerm =
      xLocalToFraction xZGerm
    rw [xLocalToFraction_xYGerm, yzLocalToFraction_yzZGerm, xLocalToFraction_xZGerm,
      div_mul_div_comm, mul_comm (algebraMap W CurveField qx) (algebraMap W CurveField qy),
      mul_div_mul_left _ _ fraction_qy_ne_zero]
  · rw [xYGerm_ord_eq_one, xZGerm_ord_eq_two]
    norm_num

/-- The three constructed normalization centers are pairwise distinct. -/
theorem infinityCenters_distinct :
    xInfinityPrime ≠ yzInfinityPrime ∧ xInfinityPrime ≠ zInfinityPrime ∧
      yzInfinityPrime ≠ zInfinityPrime :=
  ⟨xInfinityPrime_ne_yzInfinityPrime, xInfinityPrime_ne_zInfinityPrime,
    yzInfinityPrime_ne_zInfinityPrime⟩

end MazurProof.N25F_InfinityCenterDistinctness
