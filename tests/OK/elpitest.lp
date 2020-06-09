require open tests.OK.logic
require open tests.OK.bool
require open tests.OK.nat

elpi "tests/OK/elpitest.elpi" "main" (Πx y : nat, P (eq nat x y) → P (eq nat y x))