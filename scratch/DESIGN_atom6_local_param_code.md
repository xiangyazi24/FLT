# Q355 (dm2): Atom 6 local-parameter coefficient over dual numbers

I added the requested Lean file:

```text
scratch/Atom6LocalParam.lean
```

I cannot run `ssh uisai2` from this session, so this is written as a standalone buildable Lean file using only `Mathlib.Algebra.DualNumber` and tactics.  The core theorem is the pure dual-number arithmetic atom:

```lean
TrivSqZeroExt.snd (localParameter φ ω ψ)
  = - TrivSqZeroExt.fst φ / TrivSqZeroExt.fst ω * TrivSqZeroExt.snd ψ
```

under the hypotheses

```lean
TrivSqZeroExt.fst ψ = 0
TrivSqZeroExt.fst ω ≠ 0
```

where

```lean
localParameter φ ω ψ = - (φ * ψ) / ω.
```

## File content

```lean
import Mathlib.Algebra.DualNumber
import Mathlib.Tactic

noncomputable section

open scoped DualNumber

namespace Atom6LocalParam

variable {K : Type*} [Field K]

abbrev D (K : Type*) := DualNumber K

/-- The local parameter at `O = [0:1:0]`, evaluated on a projective representative
`[X:Y:Z]`, over dual numbers. -/
def localParameter (X Y Z : D K) : D K :=
  - (X * Z) / Y

/-- If the `Z`-coordinate is pure infinitesimal, then the local parameter is also pure
infinitesimal. -/
theorem localParameter_fst_eq_zero
    (φ ω ψ : D K) (hψ : TrivSqZeroExt.fst ψ = 0) :
    TrivSqZeroExt.fst (localParameter φ ω ψ) = 0 := by
  simp [localParameter, div_eq_mul_inv, hψ]

/-- Atom 6: the epsilon coefficient of `t = -X*Z/Y` for the projective representative
`[φ : ω : ψ]`, assuming `ψ` specializes to zero and `ω` specializes to a nonzero scalar.

This is the pure dual-number arithmetic statement used when `[φ : ω : ψ]` is
`[φ_n(Pε) : ω_n(Pε) : ψ_n(Pε)]`. -/
theorem localParameter_snd_eq
    (φ ω ψ : D K)
    (hψ : TrivSqZeroExt.fst ψ = 0)
    (hω : TrivSqZeroExt.fst ω ≠ 0) :
    TrivSqZeroExt.snd (localParameter φ ω ψ) =
      - TrivSqZeroExt.fst φ / TrivSqZeroExt.fst ω * TrivSqZeroExt.snd ψ := by
  unfold localParameter
  rw [div_eq_mul_inv]
  simp [hψ, mul_assoc, mul_left_comm, mul_comm]
  field_simp [hω]
  ring

/-- Same as `localParameter_snd_eq`, but with named base values for `φ` and `ω`.
This is often the most convenient statement when `φ0 = φ_n(P)` and `ω0 = ω_n(P)`. -/
theorem localParameter_snd_eq_base
    (φ0 ω0 : K) (φ ω ψ : D K)
    (hφ0 : TrivSqZeroExt.fst φ = φ0)
    (hω0 : TrivSqZeroExt.fst ω = ω0)
    (hψ0 : TrivSqZeroExt.fst ψ = 0)
    (hω0ne : ω0 ≠ 0) :
    TrivSqZeroExt.snd (localParameter φ ω ψ) =
      - φ0 / ω0 * TrivSqZeroExt.snd ψ := by
  subst φ0
  subst ω0
  exact localParameter_snd_eq φ ω ψ hψ0 hω0ne

/-- Special case where the `Z`-coordinate is written explicitly as `inr u`. -/
theorem localParameter_snd_eq_inr
    (φ ω : D K) (u : K)
    (hω : TrivSqZeroExt.fst ω ≠ 0) :
    TrivSqZeroExt.snd (localParameter φ ω (TrivSqZeroExt.inr u : D K)) =
      - TrivSqZeroExt.fst φ / TrivSqZeroExt.fst ω * u := by
  simpa using
    (localParameter_snd_eq (φ := φ) (ω := ω)
      (ψ := (TrivSqZeroExt.inr u : D K)) (by simp) hω)

/-- The exact algebraic shape from the projective representative
`[φ_n(Pε) : ω_n(Pε) : ψ_n(Pε)]`.  The hypotheses `hφ0` and `hω0`
identify the scalar parts with the values at the base point, while `hψ0`
says `ψ_n(P)=0`. -/
theorem atom6_local_parameter_coeff
    (φ0 ω0 : K) (φ εω ψ : D K)
    (hφ0 : TrivSqZeroExt.fst φ = φ0)
    (hω0 : TrivSqZeroExt.fst εω = ω0)
    (hψ0 : TrivSqZeroExt.fst ψ = 0)
    (hω0ne : ω0 ≠ 0) :
    TrivSqZeroExt.snd (localParameter φ εω ψ) =
      - φ0 / ω0 * TrivSqZeroExt.snd ψ := by
  exact localParameter_snd_eq_base φ0 ω0 φ εω ψ hφ0 hω0 hψ0 hω0ne

end Atom6LocalParam
```

## Commit

The file creation commit is:

```text
63168836f51b9303ab54c69bacdecec9f56a27b1
```
