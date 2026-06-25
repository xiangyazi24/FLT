# Q258 (dm3): Lean architecture for projective X/Y formula induction

## Bottom line

The clean Lean architecture is **not**:

```text
coordinate-ring identity with scalar ψ_{m-1}
⇒ directly a Mathlib `PointClass` equality
⇒ directly the induction step.
```

That fails because Mathlib’s Jacobian `PointClass` quotient is by weighted
scaling with a **unit**, while the scalar in the polynomial identity is
`ψ_{m-1}`, which is not a unit in the coordinate ring.

The clean architecture is instead:

1. Prove the coordinate-ring/congruence step identities as independent algebraic
   lemmas:

   ```text
   addZ(P, R_m) = ψ_{m-1} · ψ_{m+1}
   mk(addX(P, R_m) - ψ_{m-1}^2 · φ_{m+1}) = 0
   mk(addY(P, R_m) - ψ_{m-1}^3 · ω_{m+1}) = 0
   ```

2. When you want to connect to the **group law**, map to a field where
   `ψ_{m-1}` is nonzero, typically the fraction field of the generic coordinate
   ring.  There the scalar is a unit, so the weighted projective equality is a
   valid Mathlib `PointClass` equality.

3. Use Mathlib’s existing Jacobian group-law API for `W.add` / `Point.add` /
   `addMap`, not raw `addXYZ` globally.

4. Rewrite `W.add` to `W.addXYZ` only in the non-equivalent branch, using
   `W.add_of_not_equiv`.  The case `m = 1` is the doubling branch and must be
   handled by the already-proved `dblXYZ` identities.

So yes, Mathlib has enough group-law infrastructure to connect the representative
recursion to `nsmul`, but the connection goes through `W.add`, and the
nonunit-scalar issue means you should do that semantic induction over a field, not
directly inside the coordinate ring.

---

## Answer to (a): can `mk_ψ`, `mk_φ`, `mk_Ψ_sq` avoid the induction?

No.  They help, but they do not replace the projective formula induction.

The existing coordinate-ring lemmas are of the form:

```lean
#check WeierstrassCurve.Affine.CoordinateRing.mk_ψ
#check WeierstrassCurve.Affine.CoordinateRing.mk_φ
#check WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq
```

Conceptually:

```lean
mk W (W.ψ n) = mk W (W.Ψ n)
mk W (W.φ n) = mk W (Polynomial.C (W.Φ n))
mk W (W.Ψ n) ^ 2 = mk W (Polynomial.C (W.ΨSq n))
```

These lemmas say that Mathlib’s several packages for the **division polynomial
expressions** agree modulo the Weierstrass equation.  In particular, `mk_φ` is the
right way to avoid expanding the definition

```lean
φ_n = X * ψ_n^2 - ψ_{n+1} * ψ_{n-1}
```

when relating the bivariate and univariate `φ`/`Φ` sides.

But they do **not** say that `φ_n`, `ω_n`, `ψ_n` represent `[n]P` under the
Jacobian group law.  That is exactly the theorem you are proving.  If Mathlib had
an existing theorem saying

```lean
[n]P = [φ_n : ω_n : ψ_n]
```

or equivalently that `mk φ_n / mk ψ_n^2` is the x-coordinate of `[n]P`, then the
induction would already be done.  `mk_ψ`, `mk_φ`, and `mk_Ψ_sq` are lower-level
normalization lemmas, not the group-law theorem.

Use them aggressively on the RHS of your X/Y identities, but do not expect them to
supply the induction step.

---

## Answer to (b): does Mathlib have `Jacobian.addXYZ_eq_add`?

Not globally, and it cannot be true globally.

Mathlib defines the representative-level Jacobian addition roughly as:

```lean
noncomputable def WeierstrassCurve.Jacobian.add (P Q : Fin 3 → R) : Fin 3 → R :=
  if P ≈ Q then W.dblXYZ P else W.addXYZ P Q
```

So the globally correct representative operation is `W.add P Q`, not raw
`W.addXYZ P Q`.

The relevant existing API is:

```lean
#check WeierstrassCurve.Jacobian.add_of_equiv
#check WeierstrassCurve.Jacobian.add_of_not_equiv
#check WeierstrassCurve.Jacobian.addMap_eq
#check WeierstrassCurve.Jacobian.Point.add_point
#check WeierstrassCurve.Jacobian.Point.toAffineLift_add
#check WeierstrassCurve.Jacobian.Point.toAffineAddEquiv
#check WeierstrassCurve.Jacobian.map_add
```

The intended usage is:

```lean
-- quotient-level addition is represented by `W.add`
W.addMap ⟦P⟧ ⟦Q⟧ = ⟦W.add P Q⟧

-- point-level addition uses `addMap`
(P + Q).point = W.addMap P.point Q.point

-- semantic correctness of the Jacobian group law
(P + Q).toAffineLift = P.toAffineLift + Q.toAffineLift
```

Then, only after proving `¬ P ≈ Q`, you can use:

```lean
W.add_of_not_equiv hneq : W.add P Q = W.addXYZ P Q
```

If `P ≈ Q`, Mathlib uses the doubling branch:

```lean
W.add_of_equiv heq : W.add P Q = W.dblXYZ P
```

Therefore there is no global theorem of the form

```lean
W.add P Q = W.addXYZ P Q
```

and a theorem named `Jacobian.addXYZ_eq_add` would have to include a
non-equivalence hypothesis.

---

## The right induction scheme

The most robust induction is a **semantic induction over a field**, with the
coordinate-ring step identities used only after mapping into that field.

For the universal/generic proof, the field should be the fraction field of the
affine coordinate ring of the generic point.  Let `K` denote that fraction field.
Map the coordinate-ring representatives into `K`:

```lean
R n : Fin 3 → CoordinateRing
RK n : Fin 3 → K
Pgen : W_K.Jacobian.Point
```

Then prove:

```lean
theorem rep_nsmul_generic (n : ℕ) :
    ((n : ℕ) • Pgen).point = ⟦RK n⟧ := by
  induction n with
  | zero =>
      -- point at infinity, depending on your indexing convention
      ...
  | succ n ih =>
      -- use AddCommGroup/nsmul recursion and `Point.add_point`
      -- then rewrite by `addMap_eq`.
      ...
```

For `n = 1`, the statement is the base case:

```lean
R_1 = ![X, Y, 1].
```

For the step from `m` to `m+1`, split the small exceptional case:

* `m = 1`: use the doubling identity

  ```text
  dblXYZ(R_1) = scalar · R_2
  ```

  together with `W.add_of_equiv` / `W.add_self`.

* `m ≠ 1`: prove generically that `RK m ≉ RK 1`, then use

  ```lean
  W.add_of_not_equiv hneq
  ```

  to rewrite `W.add (RK m) (RK 1)` to `W.addXYZ (RK m) (RK 1)`.

Then the coordinate-ring step identity, after mapping to `K`, gives

```text
W.addXYZ(RK m, RK 1) = ψ_{m-1} • RK (m+1).
```

Since `ψ_{m-1}` is nonzero in `K`, it is a unit, so this becomes a valid
`PointClass` equality:

```lean
have hunit : IsUnit (ψK (m - 1)) := by
  exact isUnit_iff_ne_zero.mpr hψ_nonzero

have hclass :
    (⟦W.addXYZ (RK m) (RK 1)⟧ : W.PointClass K) = ⟦RK (m + 1)⟧ := by
  -- From `W.addXYZ ... = ψ_{m-1} • RK (m+1)` and `hunit`.
  rw [hstep]
  exact WeierstrassCurve.Jacobian.smul_eq (RK (m + 1)) hunit
```

This is the exact place where the coordinate-ring proof cannot be used directly:
`ψ_{m-1}` is not a unit in the coordinate ring, but it is a unit in the fraction
field once you prove it is nonzero.

---

## Skeleton of the semantic step

The following is schematic, but it shows the correct Lean shape.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.Tactic

namespace WeierstrassCurve

open Polynomial

namespace ProjectiveFormulaPlan

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

local notation3 "x" => (0 : Fin 3)
local notation3 "y" => (1 : Fin 3)
local notation3 "z" => (2 : Fin 3)

/-- Schematic representative.  In the real file this is `[φ_n, ω_n, ψ_n]`. -/
def R (n : ℕ) : Fin 3 → K :=
  sorry

/-- The base point `[X:Y:1]` after mapping to the chosen field. -/
def P : Fin 3 → K :=
  R 1

/-- The scalar in the addition step. -/
def stepScalar (m : ℕ) : K :=
  sorry -- ψ_{m-1}

/-- Coordinate identity, already proved in the coordinate ring and mapped to `K`. -/
theorem addXYZ_step_identity
    (m : ℕ) :
    W.toJacobian.addXYZ (R W m) (P W)
      = stepScalar W m • R W (m + 1) := by
  -- map the coordinate-ring X/Y/Z identities to `K`
  sorry

/-- Generic nonvanishing of the scalar. -/
theorem stepScalar_ne_zero
    {m : ℕ} (hm : m ≠ 1) :
    stepScalar W m ≠ 0 := by
  -- division-polynomial nonvanishing in the generic function field
  sorry

/-- Non-equivalence needed to rewrite `W.add` to raw `addXYZ`. -/
theorem R_nequiv_P
    {m : ℕ} (hm : m ≠ 1) :
    ¬ R W m ≈ P W := by
  -- Usually follows from the Z/X relation and `ψ_{m-1} ≠ 0`, or from
  -- generic non-torsion of the universal point.
  sorry

/-- One successor step for the point-class representative theorem. -/
theorem rep_succ_step
    {m : ℕ} (hm : m ≠ 1)
    (ih : ((m : ℕ) • Pgen W).point = ⟦R W m⟧) :
    (((m + 1 : ℕ) : ℕ) • Pgen W).point = ⟦R W (m + 1)⟧ := by
  -- nsmul recursion in the additive group of nonsingular Jacobian points
  -- rewrites `(m+1) • Pgen` as `m • Pgen + Pgen`.
  -- Then use `Point.add_point`, `addMap_eq`, and `add_of_not_equiv`.

  have hneq : ¬ R W m ≈ P W := R_nequiv_P (W := W) hm
  have hunit : IsUnit (stepScalar W m) :=
    isUnit_iff_ne_zero.mpr (stepScalar_ne_zero (W := W) hm)

  -- Schematic quotient calculation:
  calc
    (((m + 1 : ℕ) : ℕ) • Pgen W).point
        = W.toJacobian.addMap ⟦R W m⟧ ⟦P W⟧ := by
            -- nsmul recursion + `ih` + base-point representative
            sorry
    _ = ⟦W.toJacobian.add (R W m) (P W)⟧ := by
            rw [WeierstrassCurve.Jacobian.addMap_eq]
    _ = ⟦W.toJacobian.addXYZ (R W m) (P W)⟧ := by
            rw [WeierstrassCurve.Jacobian.add_of_not_equiv hneq]
    _ = ⟦stepScalar W m • R W (m + 1)⟧ := by
            rw [addXYZ_step_identity]
    _ = ⟦R W (m + 1)⟧ := by
            exact WeierstrassCurve.Jacobian.smul_eq (R W (m + 1)) hunit

end ProjectiveFormulaPlan
end WeierstrassCurve
```

The real proof will need your actual generic point `Pgen`, the nonsingularity
proofs, and the exact coercions from coordinate ring to fraction field.  But this
is the correct API shape.

---

## What about the scalar vanishing at a concrete point?

At a concrete specialization, `ψ_{m-1}(P)` can vanish.  Then the identity

```text
addXYZ(R_m, P) = ψ_{m-1} • R_{m+1}
```

can degenerate to the zero triple on the RHS and no longer gives a valid
projective representative.  That is not a contradiction: raw cleared-denominator
formulas often degenerate at exceptional points.

This is why the induction should not be run directly at arbitrary evaluated
points using raw `addXYZ`.  Run it generically over a fraction field, where the
relevant division polynomials are nonzero.  If you later need a theorem for all
specialized points, prove it by a separate specialization/closedness argument or
by handling exceptional cases with the actual `W.add` branch logic.

In other words:

```text
coordinate-ring identity: valid everywhere, but not a point-class equality when scalar is nonunit/zero;
fraction-field point-class proof: valid generically because scalar is a unit;
specialized point theorem: needs extra exceptional-case handling.
```

---

## Recommended final architecture

I would organize the project as four layers.

### Layer 1: algebraic coordinate identities

These are pure coordinate-ring/polynomial lemmas:

```lean
addZ_Rm_P
addX_Rm_P_mk
addY_Rm_P_mk
dblZ_Rm
dblX_Rm_mk
dblY_Rm_mk
```

This layer is where CAS certificates or structured `linear_combination` proofs
live.  It does not mention `Jacobian.Point`, `PointClass`, or `nsmul`.

### Layer 2: generic nonvanishing

Over the fraction field, prove:

```lean
ψK n ≠ 0
stepScalar K m ≠ 0
R K n is a valid nonsingular representative
R K m ≉ R K 1, for the addXYZ branch when m ≠ 1
```

This is where division-polynomial nonzero facts are used.

### Layer 3: semantic representative induction

Use Mathlib’s group law:

```lean
Jacobian.Point.add_point
Jacobian.addMap_eq
Jacobian.add_of_not_equiv
Jacobian.add_of_equiv / add_self for m = 1
Jacobian.Point.toAffineLift_add or toAffineAddEquiv when needed
```

to prove:

```lean
((n : ℕ) • Pgen).point = ⟦RK n⟧.
```

This is the genuine `nsmul` connection.  It should be over a field.

### Layer 4: specialization, if needed

If the final theorem must apply to arbitrary evaluated points, add a separate
specialization layer.  Do not try to get that for free from a nonunit-scaled
coordinate-ring identity.

---

## Practical answer

For proving the projective formula by induction on `n`, the right scheme is:

```text
base n = 1;
step m = 1 uses doubling;
step m > 1 uses `W.add_of_not_equiv` to rewrite `W.add` to `addXYZ`, then uses
coordinate-ring X/Y/Z step identities mapped to the generic fraction field, where
ψ_{m-1} is a unit.
```

You cannot avoid the induction entirely with `mk_ψ`/`mk_φ`/`mk_Ψ_sq`.  And
Mathlib does not have a global `addXYZ_eq_add`; the correct theorem is the
branch-specific `add_of_not_equiv`, because `W.add` is the operation that connects
to `Point.add` and `nsmul`.

This is the most reliable Lean path: keep the huge X/Y identities as algebraic
step lemmas, but use Mathlib’s existing Jacobian group-law layer to connect the
recursive representatives to `nsmul` over a field.
