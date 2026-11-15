# Certifying What an Agent Can Know

**Coverage and Limits of Computational Metaknowledge**

Jinghao Liang · Tianjin University of Finance and Economics  
AI × Epistemics Research Sprint (November 2026)

This repository accompanies the research paper *Certifying What an Agent Can Know: Coverage and Limits of Computational Metaknowledge*. It supplies the Lean formalizations, their pinned dependencies, a small finite example checker, and the research report.

**Paper:** [ResearchReport.pdf](paper/ResearchReport.pdf)

## Mathematical content

The paper studies when a computable observation determines a Boolean fact, how sound finite certificates cover the knowable query domain, and the complexity of a coarse observer's knowledge of a finer observer's ignorance. Its results include:

- **Theorem 1:** a semantic ceiling for sound-certificate coverage and criteria for attaining that ceiling.
- **Theorem 2:** a computable two-observer construction with locally witnessed ignorance and a \(\Pi^0_2\)-complete metajudgment.
- **Theorem 3:** a computably injective family of totality instances omitted by each given jointly computable sound-verifier family.
- **Proposition 1:** a characterization of coarse-observer knowledge of ignorance through abstention by all sound selective readers.

## Repository layout

| Path | Description |
| --- | --- |
| `paper/ResearchReport.pdf` | English research report |
| `lean/EpistemicSelfKnowledge.lean` | Basic observation and sound-reader results |
| `lean/EpistemicModal.lean` | Nested knowledge, two-observer construction, and totality encoding |
| `lean/EpistemicCeiling.lean` | Ambiguity witnesses and computability lemmas |
| `lean/EpistemicCoverageMeasure.lean` | Atomic measures, positive-mass gaps, and effective convergence |
| `lean/EpistemicAuditBridge.lean` | Certification-ceiling and selective-reader bridges |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Reproducible Lean configuration |
| `checks/finite_examples.py` | Independent finite example calculation |
| `docs/FORMALIZATION_SCOPE.md` | Exact machine-checked versus paper-only claims |

## Reproduce

Install [elan](https://github.com/leanprover/elan) and use the pinned Lean toolchain (Lean 4.19.0 and Mathlib v4.19.0). From the repository root:

```bash
lake exe cache get
lake build
python3 checks/finite_examples.py
```

The five Lean source files have an earlier successful compilation record in the original V3 project. They were unchanged in V4. **They have not been recompiled in this packaging environment**, which lacks `lake`. See [the formalization scope](docs/FORMALIZATION_SCOPE.md) for precise coverage; the full paper theorems should not be described as entirely formalized.

## Use and attribution

This repository is a research-support artifact associated with the paper. The manuscript's theoretical statements and proofs should be read alongside the Lean declarations; the latter formalize specified components of the arguments, not every assertion or generality in the manuscript.

AI assistance: ChatGPT assisted with proof code, literature searches, and language translation; the core ideas, manuscript writing, and mathematical arguments are attributed to the author.

No software license has been granted for the original repository contents.
