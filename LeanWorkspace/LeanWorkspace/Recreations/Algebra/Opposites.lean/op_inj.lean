import Mathlib

variable {α β : Type*}

theorem op_inj {x y : α} : MulOpposite.op x = MulOpposite.op y ↔ x = y := iff_of_eq <| PreOpposite.op'.injEq _ _

