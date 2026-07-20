# Lean Practice

A collection of my Lean 4 proof exercises, built with
[Mathlib](https://github.com/leanprover-community/mathlib4).

## Project layout

```text
Proofs/
└── NumberTheory/
    └── InfinitelyManyPrimes.lean  # Infinitude of primes
```

Future exercises can be grouped into topic directories such as `Algebra/`,
`Combinatorics/`, and `Logic/`. Import each new module from `Proofs.lean` so
that the full collection is checked by one build command.

## Setup and build

Install [elan](https://github.com/leanprover/elan), then run from the project
root:

```bash
lake update
lake build
```

The first `lake update` downloads Mathlib. `lake build` then checks every proof
in the collection.

## Proofs

- [`LeanPractice.NumberTheory.infinitely_many_primes`](Proofs/NumberTheory/InfinitelyManyPrimes.lean):
  for every natural number `n`, there is a prime strictly greater than `n`.
  The proof constructs the least prime factor of `(n + 1)! + 1`.
