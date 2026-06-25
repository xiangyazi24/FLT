# Q523 (dm3): `(X0-X1) | formalDelta`

## Exact proof pattern

Use the diagonal-difference lemma on `w` to get a quotient for `w0 - w1`, then give the quotient for `formalDelta` explicitly.

Assume the local notation is:

```lean
abbrev FG2 (R : Type*) [CommRing R] := MvPowerSeries (Fin 2) R

def X0 : FG2 R := MvPowerSeries.X (0 : Fin 2)
def X1 : FG2 R := MvPowerSeries.X (1 : Fin 2)
def delta : FG2 R := X0 - X1

def w0 : FG2 R := substX0 w   -- w(X0)
def w1 : FG2 R := substX1 w   -- w(X1)
def formalDelta : FG2 R := X0 * w1 - X1 * w0
```

Then the proof is:

```lean
theorem delta_dvd_formalDelta
    {R : Type*} [CommRing R] (w : PowerSeries R) :
    delta (R := R) ∣ formalDelta (R := R) w := by
  rcases PowerSeries.X_sub_X_dvd_subst_sub_subst
      (R := R) (f := w) with ⟨q, hq⟩
  -- hq : w0 w - w1 w = delta * q
  refine ⟨w1 (R := R) w - X1 (R := R) * q, ?_⟩
  dsimp [formalDelta, delta, X0, X1, w0, w1]
  linear_combination (norm := ring) -(X1 (R := R)) * hq
```

This is the shortest clean version.  The quotient is exactly

```lean
w1 w - X1 * q
```

where `q` is the quotient from

```lean
w0 w - w1 w = (X0 - X1) * q.
```

The key identity used by `linear_combination` is

```text
X0*w1 - X1*w0 = (X0-X1)*(w1 - X1*q)
```

under the hypothesis

```text
w0 - w1 = (X0-X1)*q.
```

## If the lemma is exposed only as a divisibility theorem

If `PowerSeries.X_sub_X_dvd_subst_sub_subst` returns a divisibility statement rather than an existential with an equality, use:

```lean
theorem delta_dvd_formalDelta'
    {R : Type*} [CommRing R] (w : PowerSeries R) :
    delta (R := R) ∣ formalDelta (R := R) w := by
  rcases PowerSeries.X_sub_X_dvd_subst_sub_subst
      (R := R) (f := w) with ⟨q, hq⟩
  refine ⟨w1 (R := R) w - X1 (R := R) * q, ?_⟩
  dsimp [formalDelta, delta, X0, X1, w0, w1]
  linear_combination (norm := ring) -(X1 (R := R)) * hq
```

This is the same proof; the only difference is how Lean elaborates the theorem call.

## If the orientation is reversed

If the diagonal-difference lemma gives

```lean
hq : w1 w - w0 w = (X1 - X0) * q
```

or equivalently returns the quotient for `w1 - w0`, use this version:

```lean
theorem delta_dvd_formalDelta_rev
    {R : Type*} [CommRing R] (w : PowerSeries R) :
    delta (R := R) ∣ formalDelta (R := R) w := by
  rcases PowerSeries.X_sub_X_dvd_subst_sub_subst
      (R := R) (f := w) with ⟨q, hq⟩
  refine ⟨w1 (R := R) w + X1 (R := R) * q, ?_⟩
  dsimp [formalDelta, delta, X0, X1, w0, w1]
  linear_combination (norm := ring) (X1 (R := R)) * hq
```

So: if `hq` is `w0 - w1 = (X0-X1)*q`, the quotient is `w1 - X1*q`; if `hq` is `w1 - w0 = (X1-X0)*q`, the quotient is `w1 + X1*q`.

## Version using only `dvd_sub`/`dvd_mul_*`

The quotient proof above is best, but the divisor-style proof is also short:

```lean
theorem delta_dvd_formalDelta_by_dvd
    {R : Type*} [CommRing R] (w : PowerSeries R) :
    delta (R := R) ∣ formalDelta (R := R) w := by
  have hdiff : delta (R := R) ∣ w0 (R := R) w - w1 (R := R) w :=
    PowerSeries.X_sub_X_dvd_subst_sub_subst (R := R) (f := w)
  have hmain : delta (R := R) ∣
      (X0 (R := R) - X1 (R := R)) * w1 (R := R) w := by
    simpa [delta] using dvd_mul_right (delta (R := R)) (w1 (R := R) w)
  have herr : delta (R := R) ∣
      X1 (R := R) * (w0 (R := R) w - w1 (R := R) w) := by
    exact dvd_mul_of_dvd_right hdiff (X1 (R := R))
  have h := dvd_sub hmain herr
  convert h using 1
  · dsimp [formalDelta, delta, X0, X1, w0, w1]
    ring
  · ring
```

But for the actual file, prefer the first proof: it gives the quotient explicitly and is usually less brittle.

## Final recommended insertion

Use this in the working file, adjusting only the local names for `w0/w1/substX0/substX1`:

```lean
theorem delta_dvd_formalDelta
    {R : Type*} [CommRing R] (w : PowerSeries R) :
    delta (R := R) ∣ formalDelta (R := R) w := by
  rcases PowerSeries.X_sub_X_dvd_subst_sub_subst
      (R := R) (f := w) with ⟨q, hq⟩
  refine ⟨w1 (R := R) w - X1 (R := R) * q, ?_⟩
  dsimp [formalDelta, delta, X0, X1, w0, w1]
  linear_combination (norm := ring) -(X1 (R := R)) * hq
```
