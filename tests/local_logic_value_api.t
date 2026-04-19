declarative local logic definitions support bare higher-order uses

  $ (WHY3_ELPI_PROGRAM=../examples/local_logic.elpi why3 prove local_logic_value.mlw --extra-config why3extra.test.conf -D why3 -a "lp local-logic" 2>&1 || true) | rg '^(constant x|constant f|goal local_logic_value)'
  constant x : int
  constant f : int -> int = fun (x1:int) -> x
  goal local_logic_value : apply_int f x = x
