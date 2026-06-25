# Q234 (dm4): dual-number local parameter computation

## Main point

Use the local parameter in inverse form

```lean
t = -X * Z * Y⁻¹
```

rather than relying on a `/` notation on the square-zero extension.  This is definitionally the same calculation as `-X * Z / Y` whenever division is elaborated as multiplication by inverse, and it avoids any dependency on a field structure for `TrivSqZeroExt K K`, which is not a field.

The key simplification is exactly the one in the question: if the projective `Z` coordinate has zero base part, then the denominator perturbation does not contribute to the first-order coefficient.  In Lean terms:

```lean
Z.fst = 0
```

implies

```lean
(-X * Z * Y⁻¹).snd = -X.fst * Z.snd / Y.fst.
```

The hypothesis `Y.fst ≠ 0` is geometrically necessary to be in the chart where `t = -X Z / Y` is defined, but the algebraic identity below is true with Lean’s total inverse convention even without that hypothesis.  I include a wrapper carrying `Y.fst ≠ 0` for use in the elliptic-curve application.

Mathlib API names used here:

* `TrivSqZeroExt K K`
* `TrivSqZeroExt.inl`, `TrivSqZeroExt.inr`
* projections `.fst`, `.snd`
* simplification lemmas such as `TrivSqZeroExt.fst_mul`, `TrivSqZeroExt.snd_mul`, `TrivSqZeroExt.fst_inv`, `TrivSqZeroExt.snd_inv`, `TrivSqZeroExt.fst_inr`, `TrivSqZeroExt.snd_inr`.

## Reusable Lean code

```lean
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.Tactic

noncomputable section

namespace DualLocalParameter

variable {K : Type*} [Field K]

/-- Dual numbers over `K`, represented as the trivial square-zero extension `K ⊕ Kε`. -/
abbrev Dual (K : Type*) := TrivSqZeroExt K K

/-- Base coefficient of a dual number. -/
abbrev baseCoeff (z : Dual K) : K := z.fst

/-- ε-coefficient of a dual number. -/
abbrev epsCoeff (z : Dual K) : K := z.snd

/-- A Jacobian projective triple with dual-number coordinates. -/
structure JacTriple (K : Type*) where
  X : Dual K
  Y : Dual K
  Z : Dual K

/-- The local parameter at `O = [0 : 1 : 0]` in Jacobian coordinates:
`t = -X Z / Y`.  We write division as multiplication by inverse on the trivial
square-zero extension. -/
def jacLocalT (Q : JacTriple K) : Dual K :=
  -Q.X * Q.Z * Q.Y⁻¹

/-- Core square-zero algebra computation.

If the base part of `Z` is zero, then only the base part of `X` and the ε-part of `Z`
contribute to the ε-coefficient of `-X Z / Y`; the ε-part of `X` and the ε-part of `Y`
are killed by `Z.fst = 0` and by `ε² = 0`.
-/
lemma jacLocalT_snd_of_Z_fst_eq_zero
    (Q : JacTriple K) (hZ : Q.Z.fst = 0) :
    (jacLocalT Q).snd = -Q.X.fst * Q.Z.snd / Q.Y.fst := by
  rcases Q with ⟨X, Y, Z⟩
  rcases X with ⟨X0, X1⟩
  rcases Y with ⟨Y0, Y1⟩
  rcases Z with ⟨Z0, Z1⟩
  simp only [jacLocalT, TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk] at hZ ⊢
  subst Z0
  simp [div_eq_mul_inv]
  ring

/-- Same computation, with the geometric chart hypothesis included.  The proof does not
need `hY`, but callers usually have it as `ω_n(P) ≠ 0`. -/
lemma jacLocalT_snd_of_Z_fst_eq_zero_of_Y_fst_ne_zero
    (Q : JacTriple K) (hZ : Q.Z.fst = 0) (hY : Q.Y.fst ≠ 0) :
    (jacLocalT Q).snd = -Q.X.fst * Q.Z.snd / Q.Y.fst := by
  exact jacLocalT_snd_of_Z_fst_eq_zero (Q := Q) hZ

/-- Scalar form: if `Z` is a pure ε-term, then the ε-coefficient of `-a Z / c` is
`-a₀ Zε / c₀`. -/
lemma snd_neg_mul_inr_mul_inv
    (a c : Dual K) (u : K) :
    ((-a * (TrivSqZeroExt.inr u : Dual K) * c⁻¹).snd)
      = -a.fst * u / c.fst := by
  simpa [jacLocalT, epsCoeff, baseCoeff] using
    (jacLocalT_snd_of_Z_fst_eq_zero
      (Q := ({ X := a, Y := c, Z := (TrivSqZeroExt.inr u : Dual K) } : JacTriple K))
      (by simp))

/-- Fully expanded form matching the informal expression
`a = inl a₀ + inr a₁`, `Z = inr u`, `c = inl c₀ + inr c₁`. -/
lemma snd_neg_inl_add_inr_mul_inr_mul_inv
    (a₀ a₁ u c₀ c₁ : K) :
    ((-(TrivSqZeroExt.inl a₀ + TrivSqZeroExt.inr a₁ : Dual K)
        * (TrivSqZeroExt.inr u : Dual K)
        * (TrivSqZeroExt.inl c₀ + TrivSqZeroExt.inr c₁ : Dual K)⁻¹).snd)
      = -a₀ * u / c₀ := by
  simpa using
    (snd_neg_mul_inr_mul_inv
      (K := K)
      (a := (TrivSqZeroExt.inl a₀ + TrivSqZeroExt.inr a₁ : Dual K))
      (c := (TrivSqZeroExt.inl c₀ + TrivSqZeroExt.inr c₁ : Dual K))
      (u := u))

end DualLocalParameter
```

## Applying it to the torsion local-parameter computation

In the elliptic-curve setting, instantiate the lemma with

```lean
Q.X = φ_n(Pε)
Q.Y = ω_n(Pε)
Q.Z = ψ_n(Pε)
```

as dual numbers.  At an `n`-torsion point, the base part of `ψ_n(Pε)` is zero:

```lean
have hZ : Q.Z.fst = 0 := by
  -- this is `ψ_n(P) = 0`
  simpa [Q]
```

and the geometric chart hypothesis is

```lean
have hY : Q.Y.fst ≠ 0 := by
  -- this is `ω_n(P) ≠ 0`, obtained from the nonzero projective representative
  -- at `[n]P = O` and the equation at `Z = 0`.
  exact hω
```

Then:

```lean
have ht_coeff :
    (DualLocalParameter.jacLocalT Q).snd
      = -Q.X.fst * Q.Z.snd / Q.Y.fst := by
  exact DualLocalParameter.jacLocalT_snd_of_Z_fst_eq_zero_of_Y_fst_ne_zero
    (Q := Q) hZ hY
```

After rewriting the names of the three coordinates, this is precisely

```lean
coeffε (t ([n] Pε)) = -φ_n(P) * coeffε(ψ_n(Pε)) / ω_n(P).
```

No derivative algebra is needed in this lemma.  The derivative input enters only when you identify

```lean
Q.Z.snd = coeffε(ψ_n(Pε)).
```

For the polynomial evaluation bridge, use Mathlib’s `TrivSqZeroExt.inlHom` to map coefficients into dual numbers:

```lean
def evalDualPolynomial (f : K[X]) (xε : DualLocalParameter.Dual K) : DualLocalParameter.Dual K :=
  (f.map (TrivSqZeroExt.inlHom K K)).eval xε
```

The lemma you want next has the standard shape

```lean
lemma snd_evalDualPolynomial_inl_add_inr
    (f : K[X]) (x dx : K) :
    (evalDualPolynomial f (TrivSqZeroExt.inl x + TrivSqZeroExt.inr dx)).snd
      = f.derivative.eval x * dx := by
  -- prove by polynomial induction, using `TrivSqZeroExt.inr_mul_inr` for `ε² = 0`.
  -- This is independent of the local-parameter computation above.
  sorry
```

For your division-polynomial application this yields:

* odd `n`: `ψ_n = C(preΨ'_n)`, so

  ```lean
  Q.Z.snd = (preΨ'_n).derivative.eval x * dx
  ```

* even `n`: `ψ_n = ψ₂ * C(preΨ'_n)`, and at a non-2-torsion point `ψ₂(P)` is a unit.  Since the base value of `preΨ'_n` is zero at the root, the product rule leaves

  ```lean
  Q.Z.snd = ψ₂(P) * (preΨ'_n).derivative.eval x * dx
  ```

  with the possible `dψ₂` term killed by `preΨ'_n(P) = 0`.

Thus the local-parameter first-order coefficient is:

```lean
-φ_n(P) / ω_n(P) * Q.Z.snd
```

with `Q.Z.snd` then rewritten by the appropriate odd/even derivative lemma.
