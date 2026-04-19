declarative local logic definitions can be built from an explicit why3.mk-ls handle

  $ (WHY3_ELPI_PROGRAM=../examples/local_logic_named.elpi why3 prove local_logic.mlw --extra-config why3extra.test.conf -D why3 -a "lp local-logic-named" 2>&1 || true) | rg '^(constant x|constant g|goal local_logic_demo)'
  constant x : int
  constant g : int -> int = fun (x1:int) -> x
  goal local_logic_demo : infix_at g x = x
