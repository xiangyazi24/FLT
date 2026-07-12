import Mathlib

/-!
# `rational_torsion_finite` via two good primes — the group-theory reduction

Sharpens the opaque `rational_torsion_finite` assumption of the Mazur `|T| ≤ 16` campaign
into a precise, Mordell–Weil-finite-generation-FREE contract, exactly as
`PrimeTailPackage` sharpens the prime-tail axiom.

The finiteness of `E(ℚ)_tors` follows from two independent reduction homomorphisms whose
torsion kernels are respectively `p`-primary and `q`-primary for coprime `p, q`: the product
map is injective into a finite target, so the source is finite. This layer (design source
`scratch/layer2/Q4501_torsion_finite_2primes.md`, §2) is **pure group theory** and is proved
here with no `sorry`. The genuinely arithmetic input — that good reduction at a prime has a
residue-characteristic-primary torsion kernel — is isolated as the datum `PrimePowerKernelMap`
and bundled per curve in `TwoGoodPrimesReduction`; that datum is the elliptic formal-group
seam (the same seam N15/N21/N18 build a `p`-adic instance of), NOT reproved here.
-/

set_option autoImplicit false

namespace MazurProof.TorsionFinite

open scoped WeierstrassCurve.Affine

universe u

/-- A homomorphism from `T` to a finite group whose torsion kernel is `p`-primary.

For good reduction of an elliptic curve at a rational prime `p`, `Target` is the point group
of the reduced curve over the residue field `𝔽_p`; `kernel_pow` is the statement that a point
in the kernel of reduction has `p`-power order (the formal-group separatedness fact). -/
structure PrimePowerKernelMap (T : Type u) [AddCommGroup T] (p : ℕ) where
  Target : Type
  instAddCommGroupTarget : AddCommGroup Target
  instFiniteTarget : Finite Target
  red : T →+ Target
  kernel_pow : ∀ x : T, red x = 0 → ∃ n : ℕ, (p ^ n : ℕ) • x = 0

attribute [instance] PrimePowerKernelMap.instAddCommGroupTarget
attribute [instance] PrimePowerKernelMap.instFiniteTarget

/-- Two coprime naturals cannot both annihilate a nonzero element. -/
theorem eq_zero_of_coprime_nsmul_eq_zero
    {T : Type u} [AddCommGroup T] {m n : ℕ} (hmn : m.Coprime n)
    {x : T} (hm : m • x = 0) (hn : n • x = 0) : x = 0 := by
  have hom : addOrderOf x ∣ m := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hm
  have hon : addOrderOf x ∣ n := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hn
  have hog : addOrderOf x ∣ Nat.gcd m n := Nat.dvd_gcd hom hon
  rw [hmn.gcd_eq_one] at hog
  exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp hog)

/-- The product of two reduction maps with coprime-primary kernels is injective. -/
theorem pair_reduction_injective
    {T : Type u} [AddCommGroup T] {p q : ℕ} (hpq : p.Coprime q)
    (Rp : PrimePowerKernelMap T p) (Rq : PrimePowerKernelMap T q) :
    Function.Injective (Rp.red.prod Rq.red) := by
  intro x y hxy
  have hp_xy : Rp.red x = Rp.red y := by
    simpa only [AddMonoidHom.prod_apply] using congrArg Prod.fst hxy
  have hq_xy : Rq.red x = Rq.red y := by
    simpa only [AddMonoidHom.prod_apply] using congrArg Prod.snd hxy
  have hp_zero : Rp.red (x - y) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr hp_xy
  have hq_zero : Rq.red (x - y) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr hq_xy
  obtain ⟨a, ha⟩ := Rp.kernel_pow (x - y) hp_zero
  obtain ⟨b, hb⟩ := Rq.kernel_pow (x - y) hq_zero
  have hz : x - y = 0 := eq_zero_of_coprime_nsmul_eq_zero (Nat.Coprime.pow a b hpq) ha hb
  exact sub_eq_zero.mp hz

/-- Pure group theory: two finite reduction targets with coprime-primary kernels make the
source finite. -/
theorem finite_of_two_prime_power_kernel_maps
    {T : Type u} [AddCommGroup T] {p q : ℕ} (hpq : p.Coprime q)
    (Rp : PrimePowerKernelMap T p) (Rq : PrimePowerKernelMap T q) :
    Finite T :=
  Finite.of_injective (Rp.red.prod Rq.red) (pair_reduction_injective hpq Rp Rq)

/-- The rational torsion subgroup of an elliptic curve over `ℚ`. -/
abbrev RationalTorsion (E : WeierstrassCurve ℚ) [E.IsElliptic] :=
  AddCommGroup.torsion (E⁄ℚ).Point

/-- Two distinct good primes with their primary-kernel reduction data — the precise, MW-FG-free
replacement for an opaque `rational_torsion_finite` assumption. The two `PrimePowerKernelMap`
fields are the only arithmetic inputs (good-reduction formal-kernel separatedness at `p` and `q`);
everything else is the group theory above. -/
structure TwoGoodPrimesReduction (E : WeierstrassCurve ℚ) [E.IsElliptic] where
  p : ℕ
  q : ℕ
  hp : Nat.Prime p
  hq : Nat.Prime q
  coprime : Nat.Coprime p q
  atP : PrimePowerKernelMap (RationalTorsion E) p
  atQ : PrimePowerKernelMap (RationalTorsion E) q

/-- Rational torsion is finite, given the two-good-primes reduction datum. No Mordell–Weil
finite-generation theorem is used. -/
theorem rational_torsion_finite_of_twoGoodPrimes
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (D : TwoGoodPrimesReduction E) :
    Finite (AddCommGroup.torsion (E⁄ℚ).Point) :=
  finite_of_two_prime_power_kernel_maps D.coprime D.atP D.atQ

/-- Wire-ready form matching `TorsionFinite.rational_torsion_finite_of_mw`'s exact `Set.Finite`
conclusion (the shape the campaign's `rational_torsion_finite` assumption is consumed in),
but MW-FG-free: given the two-good-primes datum instead of `mordell_weil_fg`. -/
theorem rational_torsion_set_finite_of_twoGoodPrimes
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (D : TwoGoodPrimesReduction E) :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).Finite := by
  haveI := rational_torsion_finite_of_twoGoodPrimes E D
  exact Set.toFinite _

end MazurProof.TorsionFinite
