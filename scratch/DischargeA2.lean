import Mathlib
import FLT.EllipticCurve.Torsion

/-!
Stage-1 interface for the rational Weil-pairing input used by the Mazur
torsion-bound scaffold.  The only remaining mathematical seam in this file is
`rationalWeilPairingPackage`, which packages the later Miller construction.
-/

noncomputable section

open scoped WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine

namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- A rational full-torsion map lands canonically in `E.nTorsion m`. -/
def rationalTorsionMapOfFull
    (m : ℕ) (f : ZMod m × ZMod m →+ (E⁄ℚ).Point) :
    ZMod m × ZMod m →+ E.nTorsion m where
  toFun a :=
    ⟨f a, by
      rw [Submodule.mem_torsionBy_iff]
      have ha : m • a = 0 := by
        ext <;> simp
      have hmap : m • f a = 0 := by
        calc
          m • f a = f (m • a) := (f.map_nsmul m a).symm
          _ = 0 := by simp [ha]
      change (m : ℤ) • f a = 0
      simpa only [natCast_zsmul] using hmap⟩
  map_zero' := by
    ext
    exact f.map_zero
  map_add' a b := by
    ext
    exact f.map_add a b

/-- Rational Weil pairing data on rational `m`-torsion, modulo the Miller construction. -/
structure WeilPairingPackage (m : ℕ) where
  pairing : E.nTorsion m → E.nTorsion m → rootsOfUnity m ℚ
  map_add_left :
    ∀ P₁ P₂ Q,
      pairing (P₁ + P₂) Q = pairing P₁ Q * pairing P₂ Q
  map_add_right :
    ∀ P Q₁ Q₂,
      pairing P (Q₁ + Q₂) = pairing P Q₁ * pairing P Q₂
  alternating :
    ∀ P, pairing P P = 1
  nondeg_left_on_full_grid :
    ∀ (f : ZMod m × ZMod m →+ (E⁄ℚ).Point)
      (_hf : Function.Injective f)
      (a : ZMod m × ZMod m),
      (((pairing (E.rationalTorsionMapOfFull m f a)
          (E.rationalTorsionMapOfFull m f (1, 0)) : ℚˣ) : ℚ) = 1) →
      (((pairing (E.rationalTorsionMapOfFull m f a)
          (E.rationalTorsionMapOfFull m f (0, 1)) : ℚˣ) : ℚ) = 1) →
      a = 0

namespace WeilPairingPackage

variable {E : WeierstrassCurve ℚ} [E.IsElliptic] {m : ℕ}
variable (pkg : E.WeilPairingPackage m)

omit [E.IsElliptic] in
lemma pairing_zero_left (Q : E.nTorsion m) :
    pkg.pairing 0 Q = 1 := by
  have h := pkg.map_add_left (0 : E.nTorsion m) 0 Q
  have h' :
      (1 : rootsOfUnity m ℚ) * pkg.pairing 0 Q =
        pkg.pairing 0 Q * pkg.pairing 0 Q := by
    simpa using h
  exact (mul_right_cancel h').symm

omit [E.IsElliptic] in
lemma pairing_zero_right (P : E.nTorsion m) :
    pkg.pairing P 0 = 1 := by
  have h := pkg.map_add_right P (0 : E.nTorsion m) 0
  have h' :
      (1 : rootsOfUnity m ℚ) * pkg.pairing P 0 =
        pkg.pairing P 0 * pkg.pairing P 0 := by
    simpa using h
  exact (mul_right_cancel h').symm

omit [E.IsElliptic] in
lemma pairing_nsmul_left (r : ℕ) (P Q : E.nTorsion m) :
    pkg.pairing (r • P) Q = pkg.pairing P Q ^ r := by
  induction r with
  | zero =>
      simpa using pkg.pairing_zero_left Q
  | succ r ih =>
      simp [succ_nsmul, pkg.map_add_left, ih, pow_succ,
        mul_comm]

omit [E.IsElliptic] in
lemma pairing_nsmul_right (r : ℕ) (P Q : E.nTorsion m) :
    pkg.pairing P (r • Q) = pkg.pairing P Q ^ r := by
  induction r with
  | zero =>
      simpa using pkg.pairing_zero_right P
  | succ r ih =>
      simp [succ_nsmul, pkg.map_add_right, ih, pow_succ,
        mul_comm]

end WeilPairingPackage

variable {E : WeierstrassCurve ℚ} [E.IsElliptic] {m : ℕ}

omit [E.IsElliptic] in
theorem pairing_of_full_grid_isPrimitive
    (pkg : E.WeilPairingPackage m)
    (f : ZMod m × ZMod m →+ (E⁄ℚ).Point)
    (hf : Function.Injective f) :
    IsPrimitiveRoot
      ((pkg.pairing
          (E.rationalTorsionMapOfFull m f (1, 0))
          (E.rationalTorsionMapOfFull m f (0, 1)) : ℚˣ) : ℚ)
      m := by
  let F : ZMod m × ZMod m →+ E.nTorsion m :=
    E.rationalTorsionMapOfFull m f
  let e₁ : ZMod m × ZMod m := (1, 0)
  let e₂ : ZMod m × ZMod m := (0, 1)
  let ζ : ℚ :=
    ((pkg.pairing (F e₁) (F e₂) : ℚˣ) : ℚ)
  refine ⟨?pow_eq_one, ?dvd_of_pow_eq_one⟩
  · have hroot :
        ((pkg.pairing (F e₁) (F e₂) : ℚˣ) ^ m = 1) :=
      (pkg.pairing (F e₁) (F e₂)).property
    simpa [ζ] using congrArg Units.val hroot
  · intro l hl
    let a : ZMod m × ZMod m := l • e₁
    have hFa : F a = l • F e₁ := by
      dsimp [a]
      exact F.map_nsmul l e₁
    have hpair₁ :
        (((pkg.pairing (F a) (F e₁) : ℚˣ) : ℚ) = 1) := by
      rw [hFa]
      have h :=
        congrArg (fun z : rootsOfUnity m ℚ => ((z : ℚˣ) : ℚ))
          (pkg.pairing_nsmul_left l (F e₁) (F e₁))
      simpa [pkg.alternating (F e₁)] using h
    have hpair₂ :
        (((pkg.pairing (F a) (F e₂) : ℚˣ) : ℚ) = 1) := by
      rw [hFa]
      have h :=
        congrArg (fun z : rootsOfUnity m ℚ => ((z : ℚˣ) : ℚ))
          (pkg.pairing_nsmul_left l (F e₁) (F e₂))
      exact (by
        simpa [ζ] using h.trans hl)
    have ha : a = 0 :=
      pkg.nondeg_left_on_full_grid f hf a hpair₁ hpair₂
    have hcoord : (l : ZMod m) = 0 := by
      have ha' : l • e₁ = 0 := ha
      have hfst := congrArg Prod.fst ha'
      change l • (1 : ZMod m) = (0 : ZMod m) at hfst
      rw [nsmul_eq_mul, mul_one] at hfst
      exact hfst
    exact (ZMod.natCast_eq_zero_iff l m).mp hcoord

omit [E.IsElliptic] in
theorem full_rational_torsion_has_primitive_root
    (pkg : E.WeilPairingPackage m)
    (_hm : 0 < m)
    (hfull : ∃ f : ZMod m × ZMod m →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  rcases hfull with ⟨f, hf⟩
  refine ⟨
    ((pkg.pairing
      (E.rationalTorsionMapOfFull m f (1, 0))
      (E.rationalTorsionMapOfFull m f (0, 1)) : ℚˣ) : ℚ),
    ?_⟩
  exact pairing_of_full_grid_isPrimitive (E := E) (m := m) pkg f hf

/-- The single remaining seam: Miller construction of the rational Weil-pairing package. -/
def rationalWeilPairingPackage
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) :
    E.WeilPairingPackage m := by
  sorry

end WeierstrassCurve
