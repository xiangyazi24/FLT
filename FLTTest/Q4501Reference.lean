import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.GroupTheory.Torsion

open scoped WeierstrassCurve.Affine

namespace Q4501Reference

universe u

/-- A reduction map whose kernel on the source is `p`-primary.

For the elliptic-curve application, `Target` is the point group of the reduced
curve over the finite residue field. -/
structure PrimePowerKernelMap (T : Type u) [AddCommGroup T] (p : ℕ) where
  Target : Type
  instAddCommGroupTarget : AddCommGroup Target
  instFiniteTarget : Finite Target
  red : T →+ Target
  kernel_pow : ∀ x : T, red x = 0 → ∃ n : ℕ, (p ^ n : ℕ) • x = 0

attribute [instance] PrimePowerKernelMap.instAddCommGroupTarget
attribute [instance] PrimePowerKernelMap.instFiniteTarget

/-- Two coprime integers cannot both kill a nonzero element of an additive group. -/
theorem eq_zero_of_coprime_nsmul_eq_zero
    {T : Type u} [AddCommGroup T] {m n : ℕ} (hmn : m.Coprime n)
    {x : T} (hm : m • x = 0) (hn : n • x = 0) : x = 0 := by
  have hom : addOrderOf x ∣ m :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr hm
  have hon : addOrderOf x ∣ n :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr hn
  have hog : addOrderOf x ∣ Nat.gcd m n := Nat.dvd_gcd hom hon
  rw [hmn.gcd_eq_one] at hog
  exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp hog)

/-- The product of two reduction maps with coprime-primary kernels is injective. -/
theorem pair_reduction_injective
    {T : Type u} [AddCommGroup T] {p q : ℕ}
    (hpq : p.Coprime q)
    (Rp : PrimePowerKernelMap T p) (Rq : PrimePowerKernelMap T q) :
    Function.Injective (Rp.red.prod Rq.red) := by
  intro x y hxy
  have hp_xy : Rp.red x = Rp.red y := by
    simpa only [AddMonoidHom.prod_apply] using congrArg Prod.fst hxy
  have hq_xy : Rq.red x = Rq.red y := by
    simpa only [AddMonoidHom.prod_apply] using congrArg Prod.snd hxy
  let z : T := x - y
  have hp_zero : Rp.red z = 0 := by
    dsimp [z]
    simpa using sub_eq_zero.mpr hp_xy
  have hq_zero : Rq.red z = 0 := by
    dsimp [z]
    simpa using sub_eq_zero.mpr hq_xy
  obtain ⟨a, ha⟩ := Rp.kernel_pow z hp_zero
  obtain ⟨b, hb⟩ := Rq.kernel_pow z hq_zero
  have hz : z = 0 :=
    eq_zero_of_coprime_nsmul_eq_zero (hpq.pow a b) ha hb
  exact sub_eq_zero.mp hz

/-- Pure group theory: two finite reduction targets with coprime-primary kernels
make the source finite. -/
theorem finite_of_two_prime_power_kernel_maps
    {T : Type u} [AddCommGroup T] {p q : ℕ}
    (hpq : p.Coprime q)
    (Rp : PrimePowerKernelMap T p) (Rq : PrimePowerKernelMap T q) :
    Finite T :=
  Finite.of_injective (Rp.red.prod Rq.red)
    (pair_reduction_injective hpq Rp Rq)

/-- The rational torsion subgroup of an elliptic curve. -/
abbrev RationalTorsion (E : WeierstrassCurve ℚ) [E.IsElliptic] :=
  AddCommGroup.torsion (E⁄ℚ).Point

/-- The complete local input at one good rational prime.

The expected production construction is:
* choose a minimal integral model over the DVR at `p`;
* use `WeierstrassCurve.reduction` for the reduced curve;
* construct reduction on all local points, restrict it to rational torsion;
* prove its torsion kernel is `p`-primary by the formal group.

Mathlib currently supplies the first two curve-level notions, but not the last
two point-level theorems. -/
structure RationalGoodReductionData
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) where
  prime : p.Prime
  mapData : PrimePowerKernelMap (RationalTorsion E) p

/-- Two distinct good primes, packaged in exactly the form needed by the
finite group-theoretic argument. -/
structure RationalTwoGoodPrimes
    (E : WeierstrassCurve ℚ) [E.IsElliptic] where
  p q : ℕ
  hp : p.Prime
  hq : q.Prime
  coprime : p.Coprime q
  atP : PrimePowerKernelMap (RationalTorsion E) p
  atQ : PrimePowerKernelMap (RationalTorsion E) q

/-- Geometric/arithmetic interface still missing from Mathlib.

Existence follows by choosing two primes away from the discriminant and
constructing the two local reduction maps. No Mordell--Weil finite-generation
theorem is involved. -/
noncomputable theorem exists_rational_two_good_primes
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Nonempty (RationalTwoGoodPrimes E) := by
  sorry

/-- Rational elliptic-curve torsion is finite, using only reduction at two good
primes. This is the theorem intended to replace the finiteness `sorry` needed
by the Mazur `ncard` statement. -/
noncomputable theorem rational_torsion_finite_via_two_good_primes
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Finite (AddCommGroup.torsion (E⁄ℚ).Point) := by
  obtain ⟨D⟩ := exists_rational_two_good_primes E
  exact finite_of_two_prime_power_kernel_maps D.coprime D.atP D.atQ

end Q4501Reference
