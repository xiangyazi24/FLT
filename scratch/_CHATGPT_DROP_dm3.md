# Q2119 (dm2): proving `left_nondegenerate` for the abstract Weil pairing

Date: 2026-06-28.

## Verdict

The proposed proof

```text
pick Q from `nondegenerate`; then `pairing P Q = 1` contradicts primitivity
```

is **not valid**, because the `P` occurring in the primitive witness

```lean
∃ P Q, IsPrimitiveRoot (pairing P Q) m
```

is not the same as the arbitrary `P` in the left radical.

The statement is true for the intended Weil-pairing interface **only after using the rank-two free `ZMod m` structure**.  The proof must be coordinate-based:

* choose a `ZMod m` basis `e₀, e₁`;
* let `ζ = pairing e₀ e₁`;
* prove or store that `ζ` is primitive;
* write `P = x • e₀ + y • e₁`;
* from `∀ a, pairing P a = 1`, plug in `a = e₁` to get `ζ ^ x.val = 1`, hence `x = 0`;
* plug in `a = e₀`; by alternating + bilinear, `pairing e₁ e₀ = ζ⁻¹`, so `(ζ⁻¹) ^ y.val = 1`, hence `y = 0`.

Important interface point: if the current structure stores only

```lean
nondegenerate : ∃ P Q, IsPrimitiveRoot (pairing P Q) m
```

then `left_nondegenerate` should not try to use that field directly.  Add one of these API seams:

```lean
basis_primitive : IsPrimitiveRoot (pairing e₀ e₁) m
```

or

```lean
pairing_det_formula :
  ∀ P Q, pairing P Q = (pairing e₀ e₁) ^ det(P,Q).val
```

and prove `basis_primitive` once from the existential primitive witness using the determinant formula.  That determinant step is the only nontrivial rank-two algebra.  The actual `left_nondegenerate` lemma is then short and deterministic.

Also: without a rank-two/free hypothesis, the statement is false.  You can take a nondegenerate rank-two summand plus an extra radical summand; there is still a primitive pair somewhere, but a nonzero vector in the extra summand pairs trivially with everything.

## Lean core: primitive root kills a `ZMod m` coordinate

This helper is the key small lemma.  It should be reusable exactly as written, modulo imports.

```lean
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

noncomputable section

lemma zmod_eq_zero_of_primitive_pow_eq_one
    {m : ℕ} [NeZero m]
    {G : Type*} [CommGroup G]
    {ζ : G} (hζ : IsPrimitiveRoot ζ m)
    (c : ZMod m) (hc : ζ ^ c.val = 1) :
    c = 0 := by
  rw [← ZMod.natCast_zmod_val c]
  exact (CharP.cast_eq_zero_iff (ZMod m) m c.val).2
    ((hζ.pow_eq_one_iff_dvd c.val).1 hc)
```

Reason: `IsPrimitiveRoot.pow_eq_one_iff_dvd` gives `m ∣ c.val`; in `ZMod m`, a natural number casts to zero exactly when `m` divides it.

## Lean proof shape for rank two

Below is the coding pattern I recommend.  I write `T m = Fin 2 → ZMod m` to avoid hiding the coordinate calculation behind a `Basis.repr` API.  If your actual file has an abstract `T` plus a basis `B : Basis (Fin 2) (ZMod m) T`, transfer through the basis equivalence or replace `(P 0)` / `(P 1)` by `(B.repr P) 0` / `(B.repr P) 1`.

The structure includes `pairing_nsmul_left` and `pairing_nsmul_right` as fields only to keep `left_nondegenerate` clean.  If your structure only has `pairing_add_left` and `pairing_add_right`, prove the two `nsmul` lemmas once by induction and use them here.

```lean
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

noncomputable section

abbrev T (m : ℕ) := Fin 2 → ZMod m

def e0 (m : ℕ) : T m :=
  fun i => if i = (0 : Fin 2) then 1 else 0

def e1 (m : ℕ) : T m :=
  fun i => if i = (1 : Fin 2) then 1 else 0

structure RankTwoWeilPairing (m : ℕ) [NeZero m]
    (K : Type*) [Field K] where
  pairing : T m → T m → rootsOfUnity m K

  pairing_zero_left : ∀ Q, pairing 0 Q = 1
  pairing_zero_right : ∀ P, pairing P 0 = 1

  pairing_add_left :
    ∀ P P' Q, pairing (P + P') Q = pairing P Q * pairing P' Q
  pairing_add_right :
    ∀ P Q Q', pairing P (Q + Q') = pairing P Q * pairing P Q'

  -- These are derivable by induction from the additivity fields above.
  -- Keeping them as lemmas/fields makes the radical proof simple.
  pairing_nsmul_left :
    ∀ n P Q, pairing (n • P) Q = pairing P Q ^ n
  pairing_nsmul_right :
    ∀ n P Q, pairing P (n • Q) = pairing P Q ^ n

  alternating : ∀ P, pairing P P = 1

  -- This is the Lean-friendly nondegeneracy seam for rank two.
  -- If the current interface only has `∃ P Q, primitive`, derive this once
  -- using the determinant formula.
  basis_primitive : IsPrimitiveRoot (pairing (e0 m) (e1 m)) m

namespace RankTwoWeilPairing

variable {m : ℕ} [NeZero m]
variable {K : Type*} [Field K]

lemma basis_swap (E : RankTwoWeilPairing m K) :
    E.pairing (e1 m) (e0 m) = (E.pairing (e0 m) (e1 m))⁻¹ := by
  have h := E.alternating ((e0 m) + (e1 m))
  have hmul :
      E.pairing (e0 m) (e1 m) * E.pairing (e1 m) (e0 m) = 1 := by
    rw [E.pairing_add_left, E.pairing_add_right, E.pairing_add_right] at h
    simpa [E.alternating (e0 m), E.alternating (e1 m),
      mul_assoc, mul_left_comm, mul_comm] using h
  calc
    E.pairing (e1 m) (e0 m)
        = 1 * E.pairing (e1 m) (e0 m) := by simp
    _ = (E.pairing (e0 m) (e1 m))⁻¹ *
          (E.pairing (e0 m) (e1 m) * E.pairing (e1 m) (e0 m)) := by
        simp [mul_assoc]
    _ = (E.pairing (e0 m) (e1 m))⁻¹ := by simp [hmul]

lemma zmod_eq_zero_of_primitive_pow_eq_one
    {G : Type*} [CommGroup G]
    {ζ : G} (hζ : IsPrimitiveRoot ζ m)
    (c : ZMod m) (hc : ζ ^ c.val = 1) :
    c = 0 := by
  rw [← ZMod.natCast_zmod_val c]
  exact (CharP.cast_eq_zero_iff (ZMod m) m c.val).2
    ((hζ.pow_eq_one_iff_dvd c.val).1 hc)

/-- Left nondegeneracy of a rank-two alternating pairing with primitive basis value. -/
theorem left_nondegenerate
    (E : RankTwoWeilPairing m K)
    (P : T m)
    (hP : ∀ a : T m, E.pairing P a = 1) :
    P = 0 := by
  -- Coordinate decomposition of `P` in the standard basis.
  have hdecomp : (P 0).val • e0 m + (P 1).val • e1 m = P := by
    ext i <;> fin_cases i <;>
      simp [e0, e1, Nat.smul_one_eq_cast, ZMod.natCast_zmod_val]

  -- First coordinate: test against `e₁`.
  have hxpow : E.pairing (e0 m) (e1 m) ^ (P 0).val = 1 := by
    have h := hP (e1 m)
    rw [← hdecomp, E.pairing_add_left,
      E.pairing_nsmul_left, E.pairing_nsmul_left] at h
    simpa [E.alternating (e1 m)] using h

  have hx : P 0 = 0 :=
    zmod_eq_zero_of_primitive_pow_eq_one E.basis_primitive (P 0) hxpow

  -- Second coordinate: test against `e₀`.
  have hswap_primitive : IsPrimitiveRoot (E.pairing (e1 m) (e0 m)) m := by
    rw [basis_swap E]
    exact E.basis_primitive.inv

  have hypow : E.pairing (e1 m) (e0 m) ^ (P 1).val = 1 := by
    have h := hP (e0 m)
    rw [← hdecomp, E.pairing_add_left,
      E.pairing_nsmul_left, E.pairing_nsmul_left] at h
    simpa [E.alternating (e0 m)] using h

  have hy : P 1 = 0 :=
    zmod_eq_zero_of_primitive_pow_eq_one hswap_primitive (P 1) hypow

  ext i <;> fin_cases i <;> simpa [hx, hy]

end RankTwoWeilPairing
```

## If you only have additivity, derive the `nsmul` lemmas

For an additive argument and multiplicative target, the scalar/nsmul rules are just induction.  Add these as internal lemmas if they are not already fields.

```lean
lemma pairing_nsmul_left_of_add
    (E : RankTwoWeilPairing m K) -- replace by your structure without the nsmul field
    (n : ℕ) (P Q : T m) :
    E.pairing (n • P) Q = E.pairing P Q ^ n := by
  induction n with
  | zero =>
      simpa using E.pairing_zero_left Q
  | succ n ih =>
      -- `simp` usually rewrites `(n+1) • P` to `n • P + P`.
      -- If orientation differs, use `succ_nsmul` / `succ_nsmul'` explicitly.
      simp [Nat.succ_eq_add_one, add_nsmul, ih, E.pairing_add_left,
        pow_succ, mul_assoc, mul_comm, mul_left_comm]

lemma pairing_nsmul_right_of_add
    (E : RankTwoWeilPairing m K) -- replace by your structure without the nsmul field
    (n : ℕ) (P Q : T m) :
    E.pairing P (n • Q) = E.pairing P Q ^ n := by
  induction n with
  | zero =>
      simpa using E.pairing_zero_right P
  | succ n ih =>
      simp [Nat.succ_eq_add_one, add_nsmul, ih, E.pairing_add_right,
        pow_succ, mul_assoc, mul_comm, mul_left_comm]
```

In the actual file, these lemmas should be attached to your existing structure rather than added as fields if possible.

## How to recover `basis_primitive` from the existing existential field

If the current interface insists on storing only:

```lean
nondegenerate : ∃ P Q, IsPrimitiveRoot (pairing P Q) m
```

then prove a separate rank-two determinant lemma:

```lean
pairing_eq_basis_power :
  ∀ P Q : T m,
    pairing P Q =
      (pairing (e0 m) (e1 m)) ^
        ((P 0).val * (Q 1).val + (m - (P 1).val * (Q 0).val % m))
```

The exact exponent expression can be cleaned up using `ZMod` rather than `% m`, but the mathematical content is:

```text
pairing P Q = ζ ^ det(P,Q),
where ζ = pairing e₀ e₁.
```

Then if some `pairing P Q = ζ ^ d` is primitive of order `m`, `ζ` itself must have order `m`, since the order of a power divides the order of the base.  In Lean, the proof should go through `IsPrimitiveRoot.eq_orderOf` / `orderOf` lemmas:

```lean
-- schematic seam, not final syntax
have hζ_order : orderOf ζ = m := by
  -- primitive (ζ ^ d) has order m
  -- orderOf (ζ ^ d) ∣ orderOf ζ
  -- and ζ is an m-th root, so orderOf ζ ∣ m
  -- hence antisymmetry gives orderOf ζ = m
exact IsPrimitiveRoot.iff_orderOf.2 hζ_order
```

This determinant/order lemma is the right place for any remaining algebraic work.  Do **not** bury it inside `left_nondegenerate`; once `basis_primitive` is available, `left_nondegenerate` should be the coordinate proof above.

## Recommended final interface

For the abstract Weil-pairing file, I would make the nondegeneracy API expose the theorem that downstream code actually needs:

```lean
left_nondegenerate :
  ∀ P, (∀ a, pairing P a = 1) → P = 0

right_nondegenerate :
  ∀ Q, (∀ a, pairing a Q = 1) → Q = 0
```

Then prove these internally from the rank-two/basis primitive facts.  Downstream Mazur torsion code should not reason from `∃ P Q, primitive`; it should call `left_nondegenerate` / `right_nondegenerate` directly.
