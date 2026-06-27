# Q1017 (dm2): dm2

## Status

The prompt body contains only the label:

```text
Q1017 (dm2): dm2
```

No concrete mathematical question, Lean theorem name, target file, error message, or proof task was supplied beyond the git-drop instructions.

I cannot safely infer a Lean implementation or proof strategy from this alone without inventing a task. This drop records that the Q1017 dm2 prompt is underspecified.

## Prior dm2 context

The immediately prior dm2 topic was separability of Mathlib-style division-polynomial factors using exact-order induction.

The conclusion from that analysis was:

- Divisibility alone is not enough.
- If `F_n = F_d * Q` and `F_d.eval x = 0`, then the derivative product rule gives `F_n'(x) = F_d'(x) * Q(x)`.
- Therefore the missing input is `Q(x) != 0`, equivalently local coprimality of the old factor with the quotient.
- Mathematically, this is a primitive-factor / reduced torsion statement, not a formal consequence of EDS divisibility alone.
- The cleaner route is to use the global separability of multiplication-by-n when `(n : K) != 0`, then derive simple roots of the relevant division-polynomial factor, with the usual normalization cases for `prePsi'`.

## Next needed information

To continue, the next prompt should include the exact theorem, file, failing goal, or mathematical lemma to analyze. With only `Q1017 (dm2): dm2`, there is no determinate task to solve.
