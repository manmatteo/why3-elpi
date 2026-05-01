# Why3-Elpi: λProlog transformations for Why3 ⚠️🚧⚠️

Warning: work in progress!

A library for [Why3](why3.lri.fr) embedding
[Elpi](https://github.com/LPCIC/elpi).  The Why3-Elpi library provides Elpi
translations of a subset of the Why3 API, and the Why3 plugin `why3_elpi_transformations`
uses the library to allow users to write Why3 transformations in the Elpi
dialect of λProlog. The dynamic transformation entry point is the focused
predicate `w3_transform`, which receives the non-goal declarations, the current
goal, and returns a list of focused output tasks; dedicated wrappers can expose
additional typed ELPI entry points such as `w3_apply_lite_by` and
`w3_exists_term`. The implemented API is visible in the `w3lp.elpi` file.

## Quick start
Clone the repository, install the dependencies, and build with dune.

With Nix and direnv:

```bash
git clone git@github.com:manmatteo/why3-elpi
cd why3-elpi
direnv allow
dune build
```

With opam:

```bash
git clone git@github.com:manmatteo/why3-elpi
cd why3-elpi
opam install . --deps-only # to create a fresh switch: opam switch create .
opam exec -- dune build
```

Run the automated test suite with:

```bash
dune runtest
```

The Why3 regression tests live as Cram transcripts in `tests/*.t`.

## Experimental ELPI transforms

The `examples/` directory contains concise, intentionally simplified
reimplementations of common Why3 transformation ideas, plus a few richer
API showcase transforms. Each one is exposed through a dedicated Why3
transformation wrapper; `lp` itself now always loads `transform.elpi` and is
best treated as the ad hoc development hook rather than the primary interface
for the bundled examples.

- `examples/intro_implies.elpi`
  - Transform: `elpi_intro_implies`
  - Behavior: repeatedly rewrites a goal `A -> B` into a local hypothesis `A`
    and a smaller goal `B`.

- `examples/intros_full.elpi`
  - Transform: `elpi_intros_full`
  - Behavior: repeatedly introduces top-level `forall` binders as fresh
    local variable declarations and top-level implications as local
    hypotheses. This is a more
    faithful, but still lightweight, `intros` prototype.

- `examples/split_goal_and.elpi`
  - Transform: `elpi_split_goal_and`
  - Behavior: splits top-level goal conjunctions `A /\\ B` into multiple
    output tasks (one conjunct per task).

- `examples/drop_non_goal_props.elpi`
  - Transform: `elpi_drop_non_goal_props`
  - Behavior: keeps goals and non-proposition declarations, drops
    lemmas/axioms.

- `examples/apply_lite.elpi`
  - Transforms:
    - `elpi_apply_lite`
    - `elpi_apply_lite_by H`
  - Behavior: tactic-like `apply` prototype.
    - `apply-lite` uses the first matching non-quantified axiom/lemma.
    - `elpi_apply_lite_by H` resolves `H` through Why3's typed transformation
      argument machinery first, so the ELPI code receives the selected
      `prsymbol` directly rather than recovering it from a string name.

- `examples/apply_ho.elpi`
  - Transforms:
    - `elpi_apply_ho H`
    - `elpi_apply_ho H with t1, ..., tn`
  - Behavior: higher-order `apply` prototype.
    - Opens top-level `forall` binders with ELPI unification variables.
    - Opens top-level `let` binders by substituting their bound term.
    - `elpi_apply_ho` also allows explicit witness terms for the first
      opened `forall` binders before falling back to unification on the
      remaining binders.
    - Uses the instantiated premises to discharge matching local hypotheses,
      so it can apply lemmas that Why3's native `apply` rejects.

- `examples/exists_term.elpi`
  - Transform: `elpi_exists_term T`
  - Behavior: instantiates the top-level existential in the current goal with
    an explicit Why3 term `T` parsed by Why3 before entering ELPI. Because the
    transformation CLI still forwards one raw argument string to the wrapper
    layer, simple term syntax is currently the most ergonomic here.

- `examples/tc.elpi`
  - Transform: `elpi_tc`
  - Behavior: compiles `[@class]` and `[@instance]` declarations into a small
    witness-synthesis engine for existential goals. The paired examples in
    `tests/tc.mlw` and `tests/tc_complex.mlw` show both a baseline usage and a
    deeper nested-resolution showcase.

- `examples/derive.elpi`
  - Transforms:
    - `elpi_derive`
    - `elpi_derive_eq`
    - `elpi_derive_ord`
  - Behavior: structurally synthesizes `eq` and `ord` witnesses from the
    requested target type shape by composing helper combinators already present
    in the Why3 task. Unlike `tc.elpi`, it does not inspect `[@instance]`
    declarations; it follows the helper signatures that are in scope, so custom
    unary/binary dictionary builders in `tests/derive.mlw` work without editing
    the ELPI transform.

Run one example with:

```bash
why3 prove tests/simple.mlw --extra-config why3extra.conf -D why3 -a "elpi_intro_implies"
```

Swap the transformation name to run the other examples.

For ad hoc local development, you can still execute the Elpi code present in
`transform.elpi` on all the tasks contained in the Why3 file `tests/simple.mlw`
and have Why3 print the resulting tasks by running:
```bash
dune exec -- why3 prove tests/simple.mlw --extra-config why3extra.conf -D why3 -a "lp param"
```

This loads `transform.elpi` and calls the query
`w3_transform "param" Rest Goal Tasks`, where `"param"` is a string that one can
use to pass arguments to the Elpi code, `Rest` is unified with the non-goal
declarations of the current task, `Goal` is unified with the focused goal
representation, and `Tasks` is the list of resulting `focused-task` values that
the Elpi code should build. For the bundled examples above, prefer the named
`elpi_*` wrappers instead. The HOAS encoding of these objects is illustrated in
[w3lp.elpi](w3lp.elpi).

Term attributes are represented with a dedicated `tattr` constructor that
wraps a term: `tattr Attrs T`. Build abstract Why3 attributes with `why3.attr`,
inspect them with `why3.attr-string`, and inspect term attributes directly via
pattern matching on `tattr Attrs T`.

Pattern matching terms use `tcase Scrutinee Branches`, where each branch is a
first-class `branch`. Pattern variables are introduced explicitly with nested
`babs` binders, patterns refer to those symbols with `pvar`, and the final
branch payload is `branch Pattern Body`.

For example, the `transform.elpi` file provided in this repository contains the line
```prolog
w3_transform "print" Rest Goal [focused-task Rest Goal] :-
  print Rest,
  print Goal.
```

Thus running

```bash
dune exec -- why3 prove tests/simple.mlw --extra-config why3extra.conf -D why3 -a "lp print"
```

Makes `why3-elpi` print the encoding of all subsequent tasks, followed by Why3 printing the same tasks.

## Mainline ELPI status

This repository now targets mainline ELPI from nixpkgs/opam rather than the old fork-specific pin.
The fork-only contextual API used by the original code is reintroduced locally through
`Elpi_api_compat`.

Current limitation: `why3` quotations inside Elpi source are not ported yet.
If code in `transform.elpi` uses `{{why3:...}}`, the plugin currently raises a clear runtime failure.

## More details

To use the transformation globally, add to `why3.conf` the line

```
plugin="/path/to/why3-elpi/_build/default/bin/why3_elpi_transformations"
```

You will have the dynamic `lp` transformation available, alongside the named
`elpi_*` wrappers registered by the plugin. Calling `lp param` will look for a
`transform.elpi` file, load it, and execute the query
`w3_transform "param" Rest Goal TaskOut`. Here `param` is a string
representing parameters one might want to pass to the Prolog code, `Rest` is
the list of non-goal declarations, `Goal` is the focused goal representation,
and `TaskOut` is the list of resulting focused tasks the transformation should
build.

If a transform needs typed Why3 objects rather than raw strings, add a
dedicated OCaml wrapper with Why3's `Args_wrapper`; `lp` itself remains a
string-based development entrypoint.

Focused goals can reify local declarations during readback with the two
builders `local-symbol` and `local-prop`, in addition to the terminal
`goal-formula`. `local-symbol` uses `symbol-param` for uninterpreted local
symbols and `symbol-logic` for local logic definitions. Its head is an
`lsymbol`, and the HOAS binders expose that handle through `ctx-ls`; term
occurrences are then written explicitly as `tapp Ls [] none`.

If you need a fresh local symbol head, use `why3.mk-ls Name Args Result Ls`.
For the common pattern of opening a forall as a local parameter, prefer the
macro `@open-forall-local-param!`. If you need a fresh `var` handle for an ad
hoc `pi x\ ctx-vs x V => ...` context, use `why3.mk-var Name Ty V`.

For example, the dynamic form underlying the bundled
`elpi_intros_full_local` wrapper, which creates local
declarations for every implication and universal quantification in the head of a
goal, can be written in this way:
```
w3_transform _ Rest (goal-formula GoalPr Goal)
             [focused-task Rest GoalOut] :-
  inspect GoalPr Goal GoalOut.

pred inspect i:prsymbol, i:term, o:focused-goal.
inspect GoalPr (tattr _ T) GoalOut :- inspect GoalPr T GoalOut.
inspect GoalPr (tquant tforall V Bnd) GoalOut :-
  @open-forall-local-param! V Bnd GoalOut (Body\ InnerGoal\
    inspect GoalPr Body InnerGoal).
inspect GoalPr (tbinop timplies Premise Body) (local-prop "H" Prem GoalOut) :-
  Prem = Premise,
  inspect GoalPr Body GoalOut.
inspect GoalPr Goal (goal-formula GoalPr Goal).
```

When the declaration you want to build does not come from an already opened
Why3 binder, you can mint a fresh `lsymbol` explicitly and still use the same
builder surface:
```
why3.mk-ls "tmp" [] Ty FreshLs,
GoalOut = local-symbol FreshLs (_\ symbol-param) Body.
```