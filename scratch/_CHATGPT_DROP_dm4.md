# Q310 (dm4): EDS nonvanishing by specialization to division polynomials

## Bottom line

Approach (c) is viable, but the right formulation is slightly different from the
phrasing “injective specialization” or “algebraically independent enough”.

For the universal normalized EDS polynomial

```lean
normEDS b c d j : ℤ[b,c,d]
```

it is enough to exhibit **one** specialization to a ring in which its image is
nonzero.  No global injectivity of the specialization is needed.

Indeed, for any ring homomorphism `φ`, if `φ x ≠ 0`, then `x ≠ 0`, because
`x = 0` would imply `φ x = 0`.  Thus the only Lean obligations are:

1. define a specialization
   `φ : ℤ[b,c,d] → Polynomial (Polynomial ℤ)` with
   `b ↦ W.ψ₂`, `c ↦ C W.Ψ₃`, `d ↦ C W.preΨ₄`;
2. prove
   `φ (normEDS b c d j) = W.ψ j`, which is exactly `map_normEDS` plus the
   Mathlib definition of `W.ψ`;
3. prove `W.ψ j ≠ 0` over one characteristic-zero base, for example `ℤ`.

The subtle point is item 3.  Mathlib’s degree file gives very strong nonzero
results for `preΨ` and especially `ΨSq`; it does not appear to give a direct
ready-made theorem named `ψ_ne_zero`.  The shortest robust bridge is:

```text
ΨSq_ne_zero
  ⇒ C(ΨSq) has nonzero image in the affine coordinate ring
  ⇒ image(Ψ)^2 ≠ 0
  ⇒ image(Ψ) ≠ 0
  ⇒ image(ψ) ≠ 0 by mk_ψ
  ⇒ ψ ≠ 0.
```

Equivalently, prove `ψ_ne_zero` by contradiction using the coordinate-ring
lemmas `mk_ψ` and `mk_Ψ_sq`.

This avoids all algebraic-independence questions.

---

## 1. Existing Mathlib facts to use

The relevant imports are already very concentrated:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Data.MvPolynomial.Basic
```

Useful checks:

```lean
#check normEDS
#check map_normEDS

#check WeierstrassCurve.ψ
#check WeierstrassCurve.preΨ_ne_zero
#check WeierstrassCurve.ΨSq_ne_zero

#check WeierstrassCurve.Affine.CoordinateRing.mk_ψ
#check WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq
#check WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero
```

The core definition is this shape:

```lean
-- In Mathlib:
-- noncomputable def WeierstrassCurve.ψ (W : WeierstrassCurve R) (n : ℤ) : R[X][Y] :=
--   normEDS W.ψ₂ (Polynomial.C W.Ψ₃) (Polynomial.C W.preΨ₄) n
```

And the EDS map lemma is this shape:

```lean
-- In Mathlib:
-- theorem map_normEDS
--     (b c d : R) (f : R →+* S) (n : ℤ) :
--     f (normEDS b c d n) = normEDS (f b) (f c) (f d) n
```

The degree/nonzero file gives, among other things:

```lean
-- In Mathlib:
-- theorem WeierstrassCurve.preΨ_ne_zero
--     {R : Type*} [CommRing R]
--     (W : WeierstrassCurve R) [Nontrivial R]
--     {n : ℤ} (h : (n : R) ≠ 0) :
--     W.preΨ n ≠ 0
--
-- theorem WeierstrassCurve.ΨSq_ne_zero
--     {R : Type*} [CommRing R] [NoZeroDivisors R]
--     (W : WeierstrassCurve R)
--     {n : ℤ} (h : (n : R) ≠ 0) :
--     W.ΨSq n ≠ 0
```

For the normalized bivariate `ψ`, the cleanest chain uses `ΨSq_ne_zero`, not
just `preΨ_ne_zero`.

---

## 2. The specialization map from `ℤ[b,c,d]`

A convenient model of `ℤ[b,c,d]` is `MvPolynomial (Fin 3) ℤ`.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Data.MvPolynomial.Basic

open Polynomial

abbrev UniversalEDSRing : Type := MvPolynomial (Fin 3) ℤ

namespace UniversalEDSRing

noncomputable abbrev b : UniversalEDSRing := MvPolynomial.X 0
noncomputable abbrev c : UniversalEDSRing := MvPolynomial.X 1
noncomputable abbrev d : UniversalEDSRing := MvPolynomial.X 2

end UniversalEDSRing

namespace WeierstrassCurve

open UniversalEDSRing

/--
The division-polynomial specialization

  `ℤ[b,c,d] → ℤ[X][Y]`

sending

  `b ↦ W.ψ₂`, `c ↦ C W.Ψ₃`, `d ↦ C W.preΨ₄`.

Here `Polynomial (Polynomial ℤ)` is Mathlib's `ℤ[X][Y]` convention for the
bivariate polynomial ring in `Y` over `ℤ[X]`.
-/
noncomputable def divPolySpec (W : WeierstrassCurve ℤ) :
    UniversalEDSRing →+* Polynomial (Polynomial ℤ) :=
  MvPolynomial.eval₂Hom
    (Int.castRingHom (Polynomial (Polynomial ℤ)))
    ![W.ψ₂, Polynomial.C W.Ψ₃, Polynomial.C W.preΨ₄]

@[simp] theorem divPolySpec_b (W : WeierstrassCurve ℤ) :
    divPolySpec W b = W.ψ₂ := by
  simp [divPolySpec, UniversalEDSRing.b]

@[simp] theorem divPolySpec_c (W : WeierstrassCurve ℤ) :
    divPolySpec W c = Polynomial.C W.Ψ₃ := by
  simp [divPolySpec, UniversalEDSRing.c]

@[simp] theorem divPolySpec_d (W : WeierstrassCurve ℤ) :
    divPolySpec W d = Polynomial.C W.preΨ₄ := by
  simp [divPolySpec, UniversalEDSRing.d]

/--
The defining specialization identity.  This is the exact formal content of
“division polynomials are the normalized EDS specialized at
`(ψ₂, Ψ₃, preΨ₄)`”.
-/
theorem divPolySpec_normEDS (W : WeierstrassCurve ℤ) (j : ℤ) :
    divPolySpec W (normEDS b c d j) = W.ψ j := by
  rw [map_normEDS b c d (divPolySpec W) j]
  simp [WeierstrassCurve.ψ]

end WeierstrassCurve
```

If your local universal ring is an iterated polynomial ring rather than an
`MvPolynomial`, replace `MvPolynomial.eval₂Hom` by the corresponding iterated
`Polynomial.aeval`/`eval₂` map.  The proof is unchanged: `map_normEDS` is the
only EDS-specific lemma needed.

---

## 3. The missing bridge: `ψ_n ≠ 0`

The important distinction:

* `preΨ_ne_zero` is already in the degree file.
* `ΨSq_ne_zero` is already in the degree file.
* A direct theorem `W.ψ n ≠ 0` may not be exported under that name.

The bridge below proves it from existing coordinate-ring lemmas.

The coordinate ring has basis `{1, Y}` over `R[X]`; Mathlib exposes this through
`smul_basis_eq_zero`.  Therefore a nonzero `p : R[X]` remains nonzero after
embedding as the constant-in-`Y` polynomial `C p` and passing to the affine
coordinate ring.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree

open Polynomial

namespace WeierstrassCurve
namespace Affine
namespace CoordinateRing

/--
A nonzero polynomial `p : R[X]` remains nonzero in the affine coordinate ring
when embedded as the bivariate polynomial `C p`.

This is the small zero-detection fact needed for constants in `Y`; it is much
weaker than injectivity of an arbitrary specialization from `ℤ[b,c,d]`.
-/
theorem mk_C_ne_zero
    {R : Type*} [CommRing R]
    (W : WeierstrassCurve.Affine R)
    {p : Polynomial R} (hp : p ≠ 0) :
    (mk W) (Polynomial.C p) ≠ 0 := by
  intro hp0
  apply hp

  have hp1 : p • (1 : W.CoordinateRing) = 0 := by
    calc
      p • (1 : W.CoordinateRing)
          = (mk W) (Polynomial.C p) * 1 := by
              simpa using smul (W' := W) p (1 : W.CoordinateRing)
      _ = 0 := by
              simpa [hp0]

  have hbasis :
      p • (1 : W.CoordinateRing)
        + (0 : Polynomial R) • (mk W) Polynomial.X = 0 := by
    simpa [hp1]

  exact (smul_basis_eq_zero (W' := W) (p := p) (q := 0) hbasis).1

end CoordinateRing
end Affine

/--
Division-polynomial nonvanishing in characteristic not dividing `n`.

This is the theorem that Approach (c) really wants.  It is not a new degree
calculation: it is just `ΨSq_ne_zero` plus the coordinate-ring comparison between
`ψ`, `Ψ`, and `ΨSq`.
-/
theorem psi_ne_zero_of_natCast_ne_zero
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    (W : WeierstrassCurve R)
    {n : ℤ} (hn : (n : R) ≠ 0) :
    W.ψ n ≠ 0 := by
  intro hψ

  have hmkψ :
      (Affine.CoordinateRing.mk W) (W.ψ n) = 0 := by
    simpa [hψ]

  have hmkΨ :
      (Affine.CoordinateRing.mk W) (W.Ψ n) = 0 := by
    simpa [Affine.CoordinateRing.mk_ψ W n] using hmkψ

  have hmkΨSq :
      (Affine.CoordinateRing.mk W) (Polynomial.C (W.ΨSq n)) = 0 := by
    rw [← Affine.CoordinateRing.mk_Ψ_sq W n]
    simpa [hmkΨ]

  exact (Affine.CoordinateRing.mk_C_ne_zero W (W.ΨSq_ne_zero hn)) hmkΨSq

end WeierstrassCurve
```

Notes on this bridge:

* The proof does not require `W` to be nonsingular.  These division-polynomial
  definitions and coordinate-ring identities are attached to a Weierstrass curve
  object, not to an elliptic-curve group law assumption.
* The assumption `(n : R) ≠ 0` is essential.  In characteristic `p`, the degree
  theorem is not available when `p ∣ n`; choosing `R = ℤ` avoids the issue.
* This bridge uses `ΨSq_ne_zero`, not only positive `natDegree_preΨ`.  Positive
  degree is also awkward at small indices (`±1`, `±2`), while `ΨSq_ne_zero`
  handles all nonzero `n` uniformly.

---

## 4. Universal nonvanishing theorem

Now choose any Weierstrass curve over `ℤ`.  The coefficient values do not matter;
all that matters is that `ℤ` is a domain and `(j : ℤ) ≠ 0` when `j ≠ 0`.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Data.MvPolynomial.Basic

open Polynomial

abbrev UniversalEDSRing : Type := MvPolynomial (Fin 3) ℤ

namespace UniversalEDSRing

noncomputable abbrev b : UniversalEDSRing := MvPolynomial.X 0
noncomputable abbrev c : UniversalEDSRing := MvPolynomial.X 1
noncomputable abbrev d : UniversalEDSRing := MvPolynomial.X 2

end UniversalEDSRing

namespace WeierstrassCurve

open UniversalEDSRing

noncomputable def divPolySpec (W : WeierstrassCurve ℤ) :
    UniversalEDSRing →+* Polynomial (Polynomial ℤ) :=
  MvPolynomial.eval₂Hom
    (Int.castRingHom (Polynomial (Polynomial ℤ)))
    ![W.ψ₂, Polynomial.C W.Ψ₃, Polynomial.C W.preΨ₄]

@[simp] theorem divPolySpec_b (W : WeierstrassCurve ℤ) :
    divPolySpec W b = W.ψ₂ := by
  simp [divPolySpec, UniversalEDSRing.b]

@[simp] theorem divPolySpec_c (W : WeierstrassCurve ℤ) :
    divPolySpec W c = Polynomial.C W.Ψ₃ := by
  simp [divPolySpec, UniversalEDSRing.c]

@[simp] theorem divPolySpec_d (W : WeierstrassCurve ℤ) :
    divPolySpec W d = Polynomial.C W.preΨ₄ := by
  simp [divPolySpec, UniversalEDSRing.d]

theorem divPolySpec_normEDS (W : WeierstrassCurve ℤ) (j : ℤ) :
    divPolySpec W (normEDS b c d j) = W.ψ j := by
  rw [map_normEDS b c d (divPolySpec W) j]
  simp [WeierstrassCurve.ψ]

/-- A dummy Weierstrass curve over `ℤ`.  No nonsingularity is needed here. -/
def Wzero : WeierstrassCurve ℤ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := 0

/--
Universal normalized EDS nonvanishing over `ℤ[b,c,d]`.

This is the desired unconditional Ward nonvanishing statement.
-/
theorem universal_normEDS_ne_zero
    {j : ℤ} (hj : j ≠ 0) :
    normEDS b c d j ≠ 0 := by
  intro hzero

  let W : WeierstrassCurve ℤ := Wzero

  have hψ : W.ψ j = 0 := by
    have hmap := congrArg (divPolySpec W) hzero
    simpa [divPolySpec_normEDS W j] using hmap

  exact (psi_ne_zero_of_natCast_ne_zero W (by simpa using hj)) hψ

end WeierstrassCurve
```

This proof has exactly the desired logical form:

```text
assume universal polynomial is zero
⇒ every specialization is zero
⇒ the division-polynomial specialization is zero
⇒ ψ_j = 0
⇒ contradiction with ψ_ne_zero.
```

Again, no injectivity of `divPolySpec` is used.

---

## 5. Pitfall check: algebraic independence is not needed

The specialization

```lean
b ↦ W.ψ₂,
c ↦ Polynomial.C W.Ψ₃,
d ↦ Polynomial.C W.preΨ₄
```

may well satisfy algebraic relations in `ℤ[X][Y]`; that is irrelevant.

What would require algebraic independence is the biconditional

```lean
normEDS b c d j = 0 ↔ W.ψ j = 0
```

or a statement that the specialization is globally zero-reflecting on all of
`ℤ[b,c,d]`.  We do not need either one.

The actual implication used is only the contrapositive of `map_zero`:

```lean
φ x ≠ 0 → x ≠ 0
```

which is valid for every ring homomorphism.  Therefore a single nonzero image is
sufficient.

So the correct answer to the “zero-detecting map” question is:

* No, you do not need to prove that the map is injective.
* No, you do not need algebraic independence of `ψ₂`, `Ψ₃`, `preΨ₄`.
* Yes, the specialization detects nonvanishing of this specific element once you
  prove its image is nonzero.

---

## 6. Recommended implementation order

1. Add the small coordinate-ring constant-in-`Y` lemma:

   ```lean
   WeierstrassCurve.Affine.CoordinateRing.mk_C_ne_zero
   ```

2. Add the division-polynomial nonzero bridge:

   ```lean
   WeierstrassCurve.psi_ne_zero_of_natCast_ne_zero
   ```

3. Define the universal `MvPolynomial (Fin 3) ℤ` variables `b c d`.

4. Define `divPolySpec` by `MvPolynomial.eval₂Hom`.

5. Prove `divPolySpec_normEDS` by `map_normEDS` and `simp [WeierstrassCurve.ψ]`.

6. Prove the universal theorem by specializing to `Wzero : WeierstrassCurve ℤ`.

The only proof fragility is exact namespace/simp spelling around
`CoordinateRing.smul` and `smul_basis_eq_zero`; mathematically, that lemma is
precisely the `{1,Y}` coordinate-ring basis statement already present in
Mathlib.

---

## 7. Answer to the three questions

### Q1. Can universal nonvanishing be concluded by pulling back?

Yes, but do not formulate it as requiring an injective pullback.  Define

```lean
φ := divPolySpec W : MvPolynomial (Fin 3) ℤ →+* Polynomial (Polynomial ℤ)
```

and prove

```lean
φ (normEDS b c d j) = W.ψ j.
```

If `W.ψ j ≠ 0`, then `normEDS b c d j ≠ 0`, because otherwise applying `φ` to
`0 = normEDS b c d j` would force `0 = W.ψ j`.

### Q2. What does Mathlib give for `ψ_n ≠ 0`?

The degree file gives nonzero results for `preΨ` and `ΨSq`, including:

```lean
W.preΨ_ne_zero : (n : R) ≠ 0 → W.preΨ n ≠ 0
W.ΨSq_ne_zero : (n : R) ≠ 0 → W.ΨSq n ≠ 0
```

For `ψ` itself, the robust chain is:

```text
W.ΨSq_ne_zero hn
+ CoordinateRing.mk_Ψ_sq
+ CoordinateRing.mk_ψ
+ constants-in-Y inject into the coordinate ring
⇒ W.ψ n ≠ 0.
```

This works over any `[CommRing R] [NoZeroDivisors R]` with `(n : R) ≠ 0`, and
in particular over `R = ℤ` for every integer `n ≠ 0`.

### Q3. Could algebraic relations in the specialization break the proof?

No.  Algebraic relations would matter if the proof needed the specialization to
be injective on all of `ℤ[b,c,d]`.  This proof only needs one fact:

```lean
φ (normEDS b c d j) = W.ψ j ≠ 0.
```

That single nonzero image already implies the source element is nonzero.  The
map can have a huge kernel; it just cannot contain this particular element,
because its image has been proved nonzero.
