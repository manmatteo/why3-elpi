declarative local logic definitions support higher-order self references

  $ (WHY3_ELPI_PROGRAM=../examples/local_logic.elpi why3 prove local_logic.mlw --extra-config why3extra.test.conf -D why3 -a "lp local-logic" 2>&1 || true) | rg '^(constant x|constant f|goal local_logic_demo)'
  constant x : int
  constant f : int -> int = fun (x1:int) -> x
  goal local_logic_demo : infix_at f x = x
