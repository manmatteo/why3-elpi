# Why3-Elpi: λProlog transformations for Why3 ⚠️🚧⚠️

Warning: work in progress!

A library for [Why3](why3.lri.fr) embedding
[Elpi](https://github.com/LPCIC/elpi).  The Why3-Elpi library provides Elpi
translations of a subset of the Why3 API, and the Why3 plugin `why3_elpi_trans`
uses the library to allow users to write Why3 transformations in the Elpi
dialect of λProlog.  The implemented API is visible in the `w3lp.elpi` file.

## Usage
In order to build the project

```
git clone git@github.com:manmatteo/why3-elpi
opam init .
dune build
```

Then, you can use the `why3_elpi_trans` plugin from the project directory by
adding to the Why3 command line the switch  `--extra-config why3extra.conf`

To use it globally, add to `why3.conf` the line

```
plugin="/path/to/why3-elpi/_build/default/bin/why3_elpi_trans"
```

You will have a new `lp` transformation available. Calling `lp param` will look
for a `transform.elpi` file, load it, and execute the query `transform "param"
TaskIn TaskOut`. Here `param` is a string representing parameters one might
want to pass to the prolog code, `TaskIn` is the λProlog representation of the
current Why3 task and `TaskOut` is the resulting task the transformation should
build.

For example, the transformation `lp intros`, that creates new assumptions for
every implication and universal quantification in the head of a goal, is written
in this way:
```
transform "intros" T T' :-
  find-goal T G Rest,
  intros G G',
  std.append Rest G' T'.

type intros decl -> list tdecl -> prop.
intros G Y :- print "intros" G Y, fail.
intros (goal G (imp X Y)) [decl (axiom P X) | Y'] :-
  !,
  why3.create-prsymbol "H" P,
  intros (goal G Y) Y'.

intros (goal G (all Ty F)) [decl (param S) | Y] :-
  !,
  why3.create-lsymb "x" [] Ty S,
  intros (goal G (F (lsymb S))) Y.

intros G [decl G].
```

Where the helper predicate `find-goal` that separates the goal from the other
theory declarations is

```
pred find-goal i:list tdecl o:tdecl.
find-goal [goal Name X | _] (goal Name X) :- !.
find-goal [_ | R] X :- find-goal R X.
```