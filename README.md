# Why3-Elpi: λProlog transformations for Why3

A library for embedding [Elpi](https://github.com/LPCIC/elpi) in [Why3](https://why3.org).
The Why3-Elpi plugin allows users to write Why3 transformations as queries in the Elpi dialect of λProlog.
The available API is visible in the `w3lp.elpi` file.

## Quick start

Assumes `opam` is installed and a switch is active.

```bash
git clone git@github.com:manmatteo/why3-elpi.git
cd why3-elpi
opam install . --deps-only
dune build
```

Run an example transformation:

```bash
why3 prove tests/simple.mlw --extra-config why3extra.conf -D why3 -a "elpi_intro_implies"
```

## Included Transforms & Examples

The `examples/` directory contains reimplementations of common Why3 transformations in λProlog.
Every file is then registered as a Why3 transformation in `bin/why3_elpi_transformations.ml`.

- `elpi_intro_implies`: Introduces top-level implications as local hypotheses.
- `elpi_intros_full`: Introduces top-level `forall` binders and implications.
- `elpi_split_goal_and`: Splits top-level goal conjunctions into multiple output tasks.
- `elpi_drop_non_goal_props`: Keeps goals and non-proposition declarations, drops lemmas/axioms.
- `elpi_apply_ho [with t1, ..., tn]`: Higher-order `apply` prototype with explicit witness terms.
- `elpi_exists_term T`: Instantiates the top-level existential with an explicit Why3 term `T`.
- `elpi_tc`: Compiles `[@class]` and `[@instance]` declarations into a witness-synthesis engine for existential goals.
- `elpi_derive`: Structurally synthesizes `eq` and `ord` witnesses based on helper combinators in scope.

## How it works

The bridge between Why3 and Elpi is configured in `lib/why3_elpi.ml`. It provides builders to register the Why3 transformation wrappers into Why3's environment.
When a user invokes a transformation like `elpi_apply_ho`, the engine loads `w3lp.elpi` along with the specific code (e.g. `examples/apply_ho.elpi`), and then calls the `w3_run` predicate to produce the new tasks.

```bash
# Local development: edit an example like examples/intro_implies.elpi and test the changes
dune exec -- why3 prove tests/simple.mlw --extra-config why3extra.conf -D why3 -a "elpi_intro_implies"
```
