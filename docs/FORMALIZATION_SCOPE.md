# Formalization scope and reproducibility

The paper contains three main theorems and one proposition. The Lean files formalize specific components of their arguments; full paper generality is not claimed for every theorem.

| Paper result | Components formalized in the supplied Lean source | Further arguments in the paper |
| --- | --- | --- |
| Theorem 1 | Coded observation/certificate supremum and attainment criteria (`EpistemicAuditBridge`); dyadic mass and modulus statements (`EpistemicCoverageMeasure`) | Equivalences for arbitrary uniformly computable normalized positive atomic laws, including real-name transport |
| Theorem 2 | First-witness two-observer construction, modal equivalences and fine-fiber bound (`EpistemicModal`) | General hierarchy upper bounds, completeness, and specific proper refinement conditions |
| Theorem 3 | Injective jointly omitted family for Mathlib program-code representation (`EpistemicModal`) | Transfer between acceptable numberings and one-one completeness conclusions |
| Proposition 1 | Forced-abstention equivalence (`EpistemicAuditBridge`) | Nonuniform construction caveat and randomized paired-state baseline |

## Build evidence

The original project records a successful V3 build using **Lean 4.19.0** and pinned Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The five source files and dependency pins are unchanged from that recorded build. The earlier log checked reported axioms (only standard `propext`, `Classical.choice`, and `Quot.sound` where applicable).

The current packaging environment does not contain `lake` and has **not independently re-run** this build. To reproduce on a machine with Lean installed:

```bash
lake exe cache get
lake build
```

The script `checks/finite_examples.py` checks a separate, finite illustrative example; it does not verify unbounded-program claims.
