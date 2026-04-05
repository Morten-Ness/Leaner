import Mathlib

variable {R : Type*}

variable {A : Type*}
  [Monoid R] [Monoid A] [MulAction R A] [SMulCommClass R A A]
  [IsScalarTower R A A] [StarMul R] [StarMul A] [StarModule R A]

theorem coe_smul (r : unitary R) (a : unitary A) : ↑(r • a) = r • (a : A) := rfl

