# Q2109 dm1

I rechecked GitHub after reconnect.  The connector has access to `xiangyazi24/FLT`, but the requested file is still absent from the visible `ai-scratch` tree:

```text
FLT/Assumptions/MazurProof/WeilPairingInterface.lean
```

Direct fetch on `ai-scratch` returns `404 Not Found`.  Repo search finds no hits for `WeilPairingInterface`, `primitive_root_in_base`, or `left_nondegenerate`.  The `ai-scratch` head visible to the connector is `848ffbf5163603f16828def879890e51e5cc3725`.

I therefore could not inspect or edit the exact source file.  The two pure proofs should be as follows, if the goals have the expected selected-pair shape.

Given a chosen pair with

```lean
hPQ : e P Q != 1
```

left proof:

```lean
by
  intro h
  exact hPQ (h Q)
```

right proof, if the goal is `not forall a, e a Q = 1`:

```lean
by
  intro h
  exact hPQ (h P)
```

If the right goal is instead `not forall a, e a P = 1`, first prove from bilinearity and alternatingness that

```lean
e Q P = (e P Q)^-1
```

by expanding `e (P + Q) (P + Q) = 1`; this gives `e P Q * e Q P = 1`.  Then `e Q P = 1` would imply `e P Q = 1`, contradicting `hPQ`.  The proof body is:

```lean
by
  intro h
  have hQP_ne : e Q P != 1 := by
    intro hQP
    -- use the lemma e Q P = (e P Q)^-1 here
    have hPQ_one : e P Q = 1 := by
      -- follows by rewriting with hQP
      sorry
    exact hPQ hPQ_one
  exact hQP_ne (h Q)
```

The remaining `weil_interface_bridge`-type holes are genuine elliptic-curve content: construction of the concrete Weil pairing, its bilinearity, alternatingness, nondegeneracy/primitive value, and Galois equivariance.  They should stay as named hard seams.

Important: if `left_nondegenerate` and `right_nondegenerate` are global statements of the form `forall P, (forall Q, e P Q = 1) -> P = 0`, they do not follow from one nontrivial value alone.  The interface then needs stronger data, such as explicit nondegeneracy fields or a basis plus primitive pairing value.
