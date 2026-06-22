# Q341-dm1: deriving the `preΨ` invariant from Ward `invarRel_all`

## Executive answer

The exact nonvanishing hypothesis needed is the ψ-level one in the bivariate polynomial ring:

```lean
hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0
```

This is used only to invoke your already-proved Ward invariant

```lean
invarRel_all
  (R := R[X][Y])
  (b := W.ψ₂)
  (c := C W.Ψ₃)
  (d := C W.preΨ₄)
```

for the bivariate sequence

```lean
W.ψ n = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n.
```

The descent to `preΨ` then uses exactly the same mechanism as your adjacent-Somos proof:

```lean
Affine.CoordinateRing.mk_ψ
Affine.CoordinateRing.mk_ψ₂_sq
mk_C_injective
Ψ₂Sq_ne_zero h4
```

The parity translations are:

```text
q := mk W W.ψ₂,
s := W.Ψ₂Sq,
mkC(f) := mk W (C f).
```

If `Even m`, then

```text
mk(Nseq ψ₂ (C Ψ₃) (C preΨ₄) m)
= q * mkC( preΨ(m+2) preΨ(m-1)^2
           + preΨ(m+1)^2 preΨ(m-2)
           + s^2 preΨ(m)^3 ),

mk(Dseq ψ₂ (C Ψ₃) (C preΨ₄) m)
= q * mkC( preΨ(m+1) preΨ(m) preΨ(m-1) ).
```

If `¬ Even m`, then

```text
mk(Nseq ψ₂ (C Ψ₃) (C preΨ₄) m)
= q^2 * mkC( preΨ(m+2) preΨ(m-1)^2
             + preΨ(m+1)^2 preΨ(m-2)
             + preΨ(m)^3 ),

mk(Dseq ψ₂ (C Ψ₃) (C preΨ₄) m)
= q^2 * mkC( preΨ(m+1) preΨ(m) preΨ(m-1) ).
```

In both cases,

```text
mkC(preΨ₄) + q^4 = mkC(preΨ₄ + Ψ₂Sq^2),
```

because `q^2 = mkC(Ψ₂Sq)`.

So the even branch cancels `q`, and the odd branch cancels `q^2`.

---

## Lean code

This is the complete proof shape.  It assumes your repository already has the following names, as in your message:

```lean
invarRel_all
Nseq
Dseq
mk_C_injective
Ψ₂Sq_ne_zero
```

If your `mk_C_injective` theorem is namespaced, replace the two calls marked below by your local theorem name.  Current Mathlib names used here are `Affine.CoordinateRing.mk_ψ`, `Affine.CoordinateRing.mk_ψ₂_sq`, and `WeierstrassCurve.Ψ`.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

open Polynomial
open scoped Polynomial

namespace WeierstrassCurve

noncomputable section

variable {R : Type*} [CommRing R]

private def preΨInvN (W : WeierstrassCurve R) (m : ℤ) : R[X] :=
  W.preΨ (m + 2) * W.preΨ (m - 1)^2
    + W.preΨ (m + 1)^2 * W.preΨ (m - 2)
    + (if Even m then W.Ψ₂Sq^2 else 1) * W.preΨ m^3

private def preΨInvD (W : WeierstrassCurve R) (m : ℤ) : R[X] :=
  W.preΨ (m + 1) * W.preΨ m * W.preΨ (m - 1)

private lemma preΨ_invariant_even
    [IsDomain R]
    (W : WeierstrassCurve R)
    (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0)
    {m : ℤ} (hm : Even m) :
    W.Ψ₃ * preΨInvN W m
      = (W.preΨ₄ + W.Ψ₂Sq^2) * preΨInvD W m := by
  classical

  let mkC : R[X] →+* _ := (Affine.CoordinateRing.mk W).comp Polynomial.C
  let q : _ := Affine.CoordinateRing.mk W W.ψ₂

  have hmkC : Function.Injective mkC := by
    -- Replace this line by your exact local lemma if namespaced differently.
    simpa [mkC, Function.comp_def] using (mk_C_injective (W := W))

  have hs_ne : W.Ψ₂Sq ≠ 0 := Ψ₂Sq_ne_zero (W := W) h4

  have hq2 : q^2 = mkC W.Ψ₂Sq := by
    simpa [q, mkC, sq] using (Affine.CoordinateRing.mk_ψ₂_sq (W := W))

  have hmkCs_ne : mkC W.Ψ₂Sq ≠ 0 := by
    intro h
    apply hs_ne
    apply hmkC
    simpa [mkC] using h

  have hq2_ne : q^2 ≠ 0 := by
    simpa [hq2] using hmkCs_ne

  have hq_ne : q ≠ 0 := by
    intro hq
    apply hq2_ne
    simp [hq]

  have hq4 : q^4 = mkC (W.Ψ₂Sq^2) := by
    calc
      q^4 = (q^2)^2 := by ring
      _ = (mkC W.Ψ₂Sq)^2 := by rw [hq2]
      _ = mkC (W.Ψ₂Sq^2) := by simp [mkC]

  have hne_norm :
      ∀ k : ℤ, k ≠ 0 → normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) k ≠ 0 := by
    intro k hk
    simpa [WeierstrassCurve.ψ] using hψ_ne k hk

  have hWard :=
    invarRel_all
      (R := R[X][Y])
      (b := W.ψ₂)
      (c := C W.Ψ₃)
      (d := C W.preΨ₄)
      hne_norm m

  have hWardψ :
      C W.Ψ₃ *
          (W.ψ (m + 2) * W.ψ (m - 1)^2
            + W.ψ (m + 1)^2 * W.ψ (m - 2)
            + W.ψ₂^2 * W.ψ m^3)
        = (C W.preΨ₄ + W.ψ₂^4)
          * (W.ψ (m + 1) * W.ψ m * W.ψ (m - 1)) := by
    simpa [Nseq, Dseq, WeierstrassCurve.ψ] using hWard

  have hMk := congrArg (Affine.CoordinateRing.mk W) hWardψ

  have hm_p2 : Even (m + 2) := by omega
  have hm_m2 : Even (m - 2) := by omega
  have hm_p1 : ¬ Even (m + 1) := by omega
  have hm_m1 : ¬ Even (m - 1) := by omega

  -- ψ-to-preΨ parity normalization.  In this even branch both Nseq and Dseq
  -- carry exactly one factor `q = mk ψ₂`.
  have hq_mul :
      q * mkC (W.Ψ₃ * preΨInvN W m)
        = q * mkC ((W.preΨ₄ + W.Ψ₂Sq^2) * preΨInvD W m) := by
    linear_combination (norm :=
      (simp [mkC, q, preΨInvN, preΨInvD,
        Affine.CoordinateRing.mk_ψ, WeierstrassCurve.Ψ,
        hm, hm_p2, hm_m2, hm_p1, hm_m1,
        hq2, hq4]; ring_nf)) hMk

  have hmk_eq :
      mkC (W.Ψ₃ * preΨInvN W m)
        = mkC ((W.preΨ₄ + W.Ψ₂Sq^2) * preΨInvD W m) :=
    mul_left_cancel₀ hq_ne hq_mul

  exact hmkC hmk_eq

private lemma preΨ_invariant_odd
    [IsDomain R]
    (W : WeierstrassCurve R)
    (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0)
    {m : ℤ} (hm : ¬ Even m) :
    W.Ψ₃ * preΨInvN W m
      = (W.preΨ₄ + W.Ψ₂Sq^2) * preΨInvD W m := by
  classical

  let mkC : R[X] →+* _ := (Affine.CoordinateRing.mk W).comp Polynomial.C
  let q : _ := Affine.CoordinateRing.mk W W.ψ₂

  have hmkC : Function.Injective mkC := by
    -- Replace this line by your exact local lemma if namespaced differently.
    simpa [mkC, Function.comp_def] using (mk_C_injective (W := W))

  have hs_ne : W.Ψ₂Sq ≠ 0 := Ψ₂Sq_ne_zero (W := W) h4

  have hq2 : q^2 = mkC W.Ψ₂Sq := by
    simpa [q, mkC, sq] using (Affine.CoordinateRing.mk_ψ₂_sq (W := W))

  have hmkCs_ne : mkC W.Ψ₂Sq ≠ 0 := by
    intro h
    apply hs_ne
    apply hmkC
    simpa [mkC] using h

  have hq2_ne : q^2 ≠ 0 := by
    simpa [hq2] using hmkCs_ne

  have hq4 : q^4 = mkC (W.Ψ₂Sq^2) := by
    calc
      q^4 = (q^2)^2 := by ring
      _ = (mkC W.Ψ₂Sq)^2 := by rw [hq2]
      _ = mkC (W.Ψ₂Sq^2) := by simp [mkC]

  have hne_norm :
      ∀ k : ℤ, k ≠ 0 → normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) k ≠ 0 := by
    intro k hk
    simpa [WeierstrassCurve.ψ] using hψ_ne k hk

  have hWard :=
    invarRel_all
      (R := R[X][Y])
      (b := W.ψ₂)
      (c := C W.Ψ₃)
      (d := C W.preΨ₄)
      hne_norm m

  have hWardψ :
      C W.Ψ₃ *
          (W.ψ (m + 2) * W.ψ (m - 1)^2
            + W.ψ (m + 1)^2 * W.ψ (m - 2)
            + W.ψ₂^2 * W.ψ m^3)
        = (C W.preΨ₄ + W.ψ₂^4)
          * (W.ψ (m + 1) * W.ψ m * W.ψ (m - 1)) := by
    simpa [Nseq, Dseq, WeierstrassCurve.ψ] using hWard

  have hMk := congrArg (Affine.CoordinateRing.mk W) hWardψ

  have hm_p2 : ¬ Even (m + 2) := by omega
  have hm_m2 : ¬ Even (m - 2) := by omega
  have hm_p1 : Even (m + 1) := by omega
  have hm_m1 : Even (m - 1) := by omega

  -- ψ-to-preΨ parity normalization.  In this odd branch both Nseq and Dseq
  -- carry exactly `q^2 = mkC Ψ₂Sq`.
  have hq2_mul :
      q^2 * mkC (W.Ψ₃ * preΨInvN W m)
        = q^2 * mkC ((W.preΨ₄ + W.Ψ₂Sq^2) * preΨInvD W m) := by
    linear_combination (norm :=
      (simp [mkC, q, preΨInvN, preΨInvD,
        Affine.CoordinateRing.mk_ψ, WeierstrassCurve.Ψ,
        hm, hm_p2, hm_m2, hm_p1, hm_m1,
        hq2, hq4]; ring_nf)) hMk

  have hmk_eq :
      mkC (W.Ψ₃ * preΨInvN W m)
        = mkC ((W.preΨ₄ + W.Ψ₂Sq^2) * preΨInvD W m) :=
    mul_left_cancel₀ hq2_ne hq2_mul

  exact hmkC hmk_eq

/-- The invariant relation for the univariate auxiliary division-polynomial sequence `preΨ`.

This is Ward's invariant for the bivariate division-polynomial EDS `ψ`, descended through the
affine coordinate ring.  The only cancellation is by `mk ψ₂` in the even case and by
`mk ψ₂ ^ 2` in the odd case; both are justified by `mk_ψ₂_sq` and `Ψ₂Sq_ne_zero h4`.
-/
lemma preΨ_invariant
    [IsDomain R]
    (W : WeierstrassCurve R)
    (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0)
    (m : ℤ) :
    W.Ψ₃ *
        (W.preΨ (m + 2) * W.preΨ (m - 1)^2
          + W.preΨ (m + 1)^2 * W.preΨ (m - 2)
          + (if Even m then W.Ψ₂Sq^2 else 1) * W.preΨ m^3)
      = (W.preΨ₄ + W.Ψ₂Sq^2)
          * (W.preΨ (m + 1) * W.preΨ m * W.preΨ (m - 1)) := by
  by_cases hm : Even m
  · simpa [preΨInvN, preΨInvD, hm] using
      preΨ_invariant_even (W := W) h4 hψ_ne (m := m) hm
  · simpa [preΨInvN, preΨInvD, hm] using
      preΨ_invariant_odd (W := W) h4 hψ_ne (m := m) hm

end

end WeierstrassCurve
```

---

## What to check if Lean does not accept the proof verbatim

The only likely name/normalization differences are these:

1. Your adjacent-Somos proof apparently uses a local lemma named

   ```lean
   mk_ψ_eq
   ```

   while current Mathlib exposes the pair

   ```lean
   Affine.CoordinateRing.mk_ψ
   WeierstrassCurve.Ψ
   ```

   as the corresponding rewrite.  If your lemma is already the expanded form

   ```lean
   mk W (W.ψ n)
     = mk W (C (W.preΨ n)) * (if Even n then mk W W.ψ₂ else 1)
   ```

   then replace

   ```lean
   Affine.CoordinateRing.mk_ψ, WeierstrassCurve.Ψ
   ```

   in the two `simp` normalizers by your `mk_ψ_eq`.

2. If your `mk_C_injective` is not a ring-hom injectivity theorem for

   ```lean
   let mkC : R[X] →+* _ := (Affine.CoordinateRing.mk W).comp Polynomial.C
   ```

   then replace the two `hmkC` blocks by the exact theorem you used in
   `preΨ_adjacent_somos`.

3. If your `Ψ₂Sq_ne_zero` is namespaced as a method, replace

   ```lean
   Ψ₂Sq_ne_zero (W := W) h4
   ```

   by

   ```lean
   W.Ψ₂Sq_ne_zero h4
   ```

   or your local lemma name.

The algebraic content of the proof is fixed by the two branch normalizations:

```text
Even m:
  mk(Nseq ψ m) = q * mkC(preΨInvN m),
  mk(Dseq ψ m) = q * mkC(preΨInvD m).

Odd m:
  mk(Nseq ψ m) = q^2 * mkC(preΨInvN m),
  mk(Dseq ψ m) = q^2 * mkC(preΨInvD m).
```

After those rewrites, both branches are one `linear_combination ... hMk` followed by one cancellation and one `mk_C_injective` application.
