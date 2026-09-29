# Gao's conjecture on the Collatz map, formalized in Lean 4

A Lean 4 + Mathlib proof of a 1993 conjecture of G.-G. Gao: consecutive
integers coalesce with density one under the Collatz map `C(n) = n/2` or
`3n+1`. Both Gao's own form (`d̄_k → 1`, and also `d(x) → 1`) and the form
recorded by Lagarias (natural density one of the `n` whose trajectory meets
that of `n+1` within `log₂ n` steps) are proved.

**This is not a claim about the 3x+1 conjecture.** Coalescence does not
require reaching 1, and nothing here shows that any integer reaches 1.

## What to audit

- [`Challenge.lean`](Challenge.lean) is the statement, about 100 lines, and
  imports only Mathlib. It defines the Collatz map, the count of halvings,
  Gao's coalescence, `d̄_k` and `d(x)`, and states
  `GaoCoalescence.lagarias_form` and `GaoCoalescence.gao_form`.
- [`Solution.lean`](Solution.lean) restates the same definitions and proves
  both theorems from the development in [`GaoCoalescence/`](GaoCoalescence).
- [`comparator.json`](comparator.json) tells `lake comparator` to check that
  the two theorems have the same statements in both files and use only
  `propext`, `Classical.choice` and `Quot.sound`.
- [`formalization.yaml`](formalization.yaml) records the sources, the role
  of AI, the known divergences from Gao's wording and the review status.

Negative reports are the most useful ones: a definition that does not say
what Gao meant, a hidden hypothesis, or any step that fails.

## The development

The 26 modules under `GaoCoalescence/` follow a pair of trajectories through
a Markov chain on states `{v, 3^k v + c}` driven by fair coin flips, which
describes the residue classes modulo `2^t` exactly, and show that the chain
is absorbed almost surely (`Martas`). `Tejonas` transports this to residue
classes and natural density (`GaoEnunciado.conjetura_gao`), and `Hienas`
proves that a meeting within `log₂ n` steps is already a coalescence in Gao's
sense (`GaoLiteral.conjetura_gao_literal`). Names and comments are in
Spanish; the companion paper explains each step in English and names the
Lean theorem behind it.

- Paper, version 1: <https://doi.org/10.5281/zenodo.23003524>. Version 2 is
  under open review on Qeios.
- Earlier archive of the same development (Lean v4.32.2, with the companion
  results on conjectures of Garner and Wu):
  <https://doi.org/10.5281/zenodo.23003500>.

The formalization and the numerical checks were produced with extensive
assistance from Anthropic's Claude models (see `formalization.yaml`). The
author, Omar Javier Said Duran, is responsible for the content.

## Build and check

```text
lake exe cache get
lake build
./scripts/verify-comparator.sh    # Linux, with bubblewrap
```

The toolchain is `leanprover/lean4:v4.35.0-rc2` with Mathlib at the same tag.
GitHub Actions runs the build, the documentation, the metadata validation and
`lake comparator` on every push.

This repository is prepared for the
[Palomar registry](https://palomar-registry.org/); submissions go through
<https://submit.palomar-registry.org/>. It started from the
[PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate); the
scripts under `scripts/`, the `docbuild/` project and the CI workflow come
from that template.

Licence: Apache-2.0 (see `LICENSE`).
