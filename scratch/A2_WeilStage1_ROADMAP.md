[ask-gpt dm2 tid=f0ba4b4d +0s] dispatched, waiting for answer
[ask-gpt dm2 tid=f0ba4b4d +90s] waiting (status=processing)
[ask-gpt dm2 tid=f0ba4b4d +180s] waiting (status=processing)
[ask-gpt dm2 tid=f0ba4b4d +270s] waiting (status=processing)
[ask-gpt dm2 tid=f0ba4b4d +360s] waiting (status=processing)
[ask-gpt dm2 tid=f0ba4b4d +450s] waiting (status=processing)
[ask-gpt dm2 tid=f0ba4b4d +503s] terminal: status=completed
The clean Stage-1 seam is:

```lean
WeilPairingPackage E m
```

with a **rational pairing on rational `m`-torsion** and a **perfectness-on-the-full-grid** field. That last field is important: your current

```lean
HasFullRationalTorsion E m :=
  ∃ f : ZMod m × ZMod m →+ (E⁄ℚ).Point, Function.Injective f
```

gives two independent rational torsion generators, but by itself it does **not** literally give a Lean `Module.Basis` of `(E.nTorsion m)` unless you also prove a spanning/cardinality/base-change lemma. So either add that spanning lemma, or package the needed perfectness on the supplied full grid. For isolating the Miller construction, the grid-perfectness field is the shortest interface.

Mathlib’s `rootsOfUnity m ℚ` is a subgroup of `ℚˣ`, so a pairing value coerces as `((z : ℚˣ) : ℚ)`. citeturn689827view0 Mathlib also has the needed `ZMod` API: `ZMod.natCast_eq_zero_iff` gives `(l : ZMod m) = 0 ↔ m ∣ l`, and `AddCommGroup.zmodModule`/`ZMod.map_smul` are the canonical tools for `ZMod m`-modules killed by `m`. citeturn315454view0 citeturn67file0L46-L85 FLT’s current `nTorsion` is exactly `Submodule.torsionBy ℤ (E⁄k).Point n`, with a `Module (ZMod n)` instance from `AddCommGroup.zmodModule`. citeturn62file0L33-L44

## Stage-1 Lean interface

```lean
import Mathlib
import FLT.EllipticCurve.Torsion

noncomputable section

open scoped WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine

/-
Use the project definition if already present.

def HasFullRationalTorsion (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) : Prop :=
  ∃ f : ZMod m × ZMod m →+ (E⁄ℚ).Point, Function.Injective f
-/

namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- A full rational torsion map lands canonically in `E.nTorsion m`. -/
def rationalTorsionMapOfFull
    (m : ℕ) (f : ZMod m × ZMod m →+ (E⁄ℚ).Point) :
    ZMod m × ZMod m →+ E.nTorsion m where
  toFun a :=
    ⟨f a, by
      have ha : m • a = 0 := by
        ext <;> simp
      -- `Submodule.torsionBy ℤ` accepts this after `simpa`, as in FLT's instance.
      simpa [ha] using (f.map_nsmul a m).symm⟩
  map_zero' := by
    ext
    simp
  map_add' a b := by
    ext
    simp

end WeierstrassCurve
```

## Pairing package

This package has the ordinary bimultiplicative fields, plus the exact restricted perfectness needed by `HasFullRationalTorsion`. The `nondeg_left_on_full_grid` field is what Miller/nondegeneracy will later prove. It avoids prematurely needing a separate theorem that the image of `hfull` spans all rational `m`-torsion.

```lean
namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

structure WeilPairingPackage (m : ℕ) where
  /-- Rational Weil pairing on rational `m`-torsion. -/
  pairing : E.nTorsion m → E.nTorsion m → rootsOfUnity m ℚ

  /-- Multiplicative in the left variable. -/
  map_add_left :
    ∀ P₁ P₂ Q,
      pairing (P₁ + P₂) Q = pairing P₁ Q * pairing P₂ Q

  /-- Multiplicative in the right variable. -/
  map_add_right :
    ∀ P Q₁ Q₂,
      pairing P (Q₁ + Q₂) = pairing P Q₁ * pairing P Q₂

  /-- Alternating. -/
  alternating :
    ∀ P, pairing P P = 1

  /--
  Perfectness on any supplied full rational `m`-torsion grid.

  This is the precise Stage-1 form needed for
  `HasFullRationalTorsion E m := ∃ f : (ZMod m)^2 →+ E(ℚ), Injective f`.

  It says: if an element of the grid pairs trivially with the two standard
  grid generators, then that element of `(ZMod m)^2` is zero.
  -/
  nondeg_left_on_full_grid :
    ∀ (f : ZMod m × ZMod m →+ (E⁄ℚ).Point)
      (_hf : Function.Injective f)
      (a : ZMod m × ZMod m),
      (((pairing (E.rationalTorsionMapOfFull m f a)
          (E.rationalTorsionMapOfFull m f (1, 0)) : ℚˣ) : ℚ) = 1) →
      (((pairing (E.rationalTorsionMapOfFull m f a)
          (E.rationalTorsionMapOfFull m f (0, 1)) : ℚˣ) : ℚ) = 1) →
      a = 0

  /-- Optional symmetric field; not needed for the primitive-root theorem. -/
  nondeg_right_on_full_grid :
    ∀ (f : ZMod m × ZMod m →+ (E⁄ℚ).Point)
      (_hf : Function.Injective f)
      (a : ZMod m × ZMod m),
      (((pairing (E.rationalTorsionMapOfFull m f (1, 0))
          (E.rationalTorsionMapOfFull m f a) : ℚˣ) : ℚ) = 1) →
      (((pairing (E.rationalTorsionMapOfFull m f (0, 1))
          (E.rationalTorsionMapOfFull m f a) : ℚˣ) : ℚ) = 1) →
      a = 0

end WeierstrassCurve
```

If you instead want the classical global fields

```lean
nondeg_left  : ∀ P, (∀ Q, pairing P Q = 1) → P = 0
nondeg_right : ∀ Q, (∀ P, pairing P Q = 1) → Q = 0
```

then you also need a separate theorem:

```lean
HasFullRationalTorsion.spans_rational_m_torsion :
  ∀ R : E.nTorsion m, ∃ a : ZMod m × ZMod m,
    R = E.rationalTorsionMapOfFull m f a
```

That theorem is **not** Miller construction; it is torsion-rank/cardinality/base-change bookkeeping. For the A2 seam, `nondeg_left_on_full_grid` is cleaner.

## Derived bimultiplicative power lemmas

These are ordinary Stage-1 lemmas from `map_add_left/right`.

```lean
namespace WeierstrassCurve.WeilPairingPackage

variable {E : WeierstrassCurve ℚ} [E.IsElliptic] {m : ℕ}
variable (pkg : E.WeilPairingPackage m)

lemma pairing_nsmul_left (r : ℕ) (P Q : E.nTorsion m) :
    pkg.pairing (r • P) Q = pkg.pairing P Q ^ r := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      simp [Nat.succ_nsmul, pkg.map_add_left, ih, pow_succ,
        mul_comm, mul_left_comm, mul_assoc]

lemma pairing_nsmul_right (r : ℕ) (P Q : E.nTorsion m) :
    pkg.pairing P (r • Q) = pkg.pairing P Q ^ r := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      simp [Nat.succ_nsmul, pkg.map_add_right, ih, pow_succ,
        mul_comm, mul_left_comm, mul_assoc]

end WeierstrassCurve.WeilPairingPackage
```

## Primitive root from a full rational grid

This is the key Stage-1 theorem. It chooses the two standard generators of the injected grid, takes their pairing, and proves primitivity.

```lean
namespace WeierstrassCurve

variable {E : WeierstrassCurve ℚ} [E.IsElliptic] {m : ℕ}

theorem pairing_of_full_grid_isPrimitive
    (pkg : E.WeilPairingPackage m)
    (f : ZMod m × ZMod m →+ (E⁄ℚ).Point)
    (hf : Function.Injective f) :
    IsPrimitiveRoot
      (((pkg.pairing
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

  · -- `ζ ^ m = 1`, because `pkg.pairing ... ... ∈ rootsOfUnity m ℚ`.
    have hroot :
        ((pkg.pairing (F e₁) (F e₂) : ℚˣ) ^ m = 1) :=
      (pkg.pairing (F e₁) (F e₂)).property
    simpa [ζ] using congrArg Units.val hroot

  · intro l hl

    let a : ZMod m × ZMod m := l • e₁

    have hFa : F a = l • F e₁ := by
      dsimp [a]
      exact F.map_nsmul e₁ l

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
      -- `h` says the left side is `ζ ^ l`; `hl` says `ζ ^ l = 1`.
      exact (by
        simpa [ζ] using h.trans hl)

    have ha : a = 0 :=
      pkg.nondeg_left_on_full_grid f hf a
        (by simpa [F, e₁, e₂] using hpair₁)
        (by simpa [F, e₁, e₂] using hpair₂)

    have hcoord : (l : ZMod m) = 0 := by
      have := congrArg Prod.fst ha
      simpa [a, e₁] using this

    exact (ZMod.natCast_eq_zero_iff l m).mp hcoord

end WeierstrassCurve
```

The only possibly brittle part in actual repo compilation is coercion simplification around

```lean
((z : ℚˣ) : ℚ)
```

If `simp` does not close one of those coercion goals, replace that line with an explicit `change` to the displayed `ℚ` equality. The mathematical content is exactly as above.

## Final theorem modulo the package

```lean
namespace WeierstrassCurve

variable {E : WeierstrassCurve ℚ} [E.IsElliptic] {m : ℕ}

theorem full_rational_torsion_has_primitive_root
    (pkg : E.WeilPairingPackage m)
    (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  rcases hfull with ⟨f, hf⟩
  refine ⟨
    ((pkg.pairing
      (E.rationalTorsionMapOfFull m f (1, 0))
      (E.rationalTorsionMapOfFull m f (0, 1)) : ℚˣ) : ℚ),
    ?_
  ⟩
  exact pairing_of_full_grid_isPrimitive (E := E) (m := m) pkg f hf

end WeierstrassCurve
```

`hm` is not actually needed by the proof once `IsPrimitiveRoot` is constructed from its defining divisibility condition, but keep it in the theorem to match the old axiom.

## Wiring the old axiom

Once the Miller/divisor construction exists, expose one definition:

```lean
namespace WeierstrassCurve

noncomputable def rationalWeilPairingPackage
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) :
    E.WeilPairingPackage m :=
  -- Stage-3 Miller construction fills this.
  -- No `axiom`; this is the single remaining implementation seam.
  by
    -- construct pairing, bilinearity, alternatingness, grid perfectness
    exact
      -- ...
      sorry

end WeierstrassCurve
```

Then the former axiom becomes a theorem:

```lean
namespace WeierstrassCurve

theorem weil_pairing_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  exact
    full_rational_torsion_has_primitive_root
      (E := E) (m := m)
      (rationalWeilPairingPackage E m)
      hm hfull

end WeierstrassCurve
```

Before Stage 3, keep the theorem in the package-hypothesis form:

```lean
theorem weil_pairing_primitive_root_of_package
    (pkg : E.WeilPairingPackage m)
    (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m :=
  full_rational_torsion_has_primitive_root pkg hm hfull
```

That cleanly isolates A2’s residual to:

```lean
rationalWeilPairingPackage :
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ),
    E.WeilPairingPackage m
```

## If you insist on global nondegeneracy instead

Use this package field:

```lean
nondeg_left :
  ∀ P : E.nTorsion m,
    (∀ Q : E.nTorsion m, pkg.pairing P Q = 1) → P = 0
```

Then add a separate non-Miller lemma:

```lean
theorem HasFullRationalTorsion.spans_nTorsion
    (hfull : HasFullRationalTorsion E m) :
    ∀ R : E.nTorsion m,
      ∃ a : ZMod m × ZMod m,
        R = E.rationalTorsionMapOfFull m f a
```

From this, prove `nondeg_left_on_full_grid` and reuse the Stage-1 proof above. Without either `spans_nTorsion` or `nondeg_left_on_full_grid`, the proof cannot be completed from `hfull` as currently defined: injection gives independent generators, not a Lean spanning statement.
