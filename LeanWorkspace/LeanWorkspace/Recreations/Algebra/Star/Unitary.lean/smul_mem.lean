import Mathlib

variable {R : Type*}

variable {A : Type*}
  [Monoid R] [Monoid A] [MulAction R A] [SMulCommClass R A A]
  [IsScalarTower R A A] [StarMul R] [StarMul A] [StarModule R A]

theorem smul_mem (r : unitary R) {a : A} (ha : a ∈ unitary A) :
    r • a ∈ unitary A := Unitary.smul_mem_of_mem (R := R) r.prop ha

