# Q2109 dm1

I rechecked GitHub after reconnect.  The connector has access to `xiangyazi24/FLT`, but this file is still absent from the visible `ai-scratch` tree:

```text
FLT/Assumptions/MazurProof/WeilPairingInterface.lean
```

Direct fetch on `ai-scratch` returns `404 Not Found`.  Search also finds no hits for `WeilPairingInterface`, `primitive_root_in_base`, or `left_nondegenerate`.  The visible `ai-scratch` head is `848ffbf5163603f16828def879890e51e5cc3725`.

I could not inspect the exact five holes.  Conditional on the usual selected-pair goal shapes, the two pure proofs are:

```lean
-- Given hPQ : e P Q ≠ 1

have left_nondegenerate : ¬ ∀ a, e P a = 1 := by
  intro h
  exact hPQ (h Q)

have right_nondegenerate : ¬ ∀ a, e a Q = 1 := by
  intro h
  exact hPQ (h P)
```

If the second goal has the reversed orientation, `¬ ∀ a, e a P = 1`, use alternatingness.

```lean
private lemma swap_eq_inv_of_alternating
    {T μ : Type*} [AddCommGroup T] [Group μ]
    (e : T → T → μ)
    (map_add_left : ∀ P Q R : T, e (P + Q) R = e P R * e Q R)
    (map_add_right : ∀ P Q R : T, e P (Q + R) = e P Q * e P R)
    (alternating : ∀ P : T, e P P = 1)
    (P Q : T) :
    e Q P = (e P Q)⁻¹ := by
  have hdiag : e (P + Q) (P + Q) = 1 := alternating (P + Q)
  have hprod : e P Q * e Q P = 1 := by
    simpa [map_add_left, map_add_right, alternating P, alternating Q, mul_assoc]
      using hdiag
  calc
    e Q P = (e P Q)⁻¹ * (e P Q * e Q P) := by group
    _ = (e P Q)⁻¹ * 1 := by rw [hprod]
    _ = (e P Q)⁻¹ := by simp

private lemma swap_ne_one_of_ne_one
    {T μ : Type*} [AddCommGroup T] [Group μ]
    (e : T → T → μ)
    (map_add_left : ∀ P Q R : T, e (P + Q) R = e P R * e Q R)
    (map_add_right : ∀ P Q R : T, e P (Q + R) = e P Q * e P R)
    (alternating : ∀ P : T, e P P = 1)
    {P Q : T}
    (hPQ : e P Q ≠ 1) :
    e Q P ≠ 1 := by
  intro hQP
  have hswap := swap_eq_inv_of_alternating e map_add_left map_add_right alternating P Q
  have hPQ_one : e P Q = 1 := by
    calc
      e P Q = ((e P Q)⁻¹)⁻¹ := by simp
      _ = (e Q P)⁻¹ := by rw [← hswap]
      _ = 1 := by simp [hQP]
  exact hPQ hPQ_one

have right_nondegenerate_reversed : ¬ ∀ a, e a P = 1 := by
  intro h
  have hQP : e Q P ≠ 1 :=
    swap_ne_one_of_ne_one e map_add_left map_add_right alternating hPQ
  exact hQP (h Q)
```

The remaining `weil_interface_bridge` holes are genuine elliptic-curve work: constructing the concrete Weil pairing, proving bilinearity/alternatingness/nondegeneracy or primitive value, Galois equivariance, and connecting full rational torsion to the abstract data.

If the file's `left_nondegenerate` and `right_nondegenerate` are global statements like

```lean
∀ P, (∀ Q, e P Q = 1) → P = 0
```

then they do not follow from one nontrivial value alone.  The interface must instead assume global nondegeneracy directly, or include a basis plus primitive pairing value.
