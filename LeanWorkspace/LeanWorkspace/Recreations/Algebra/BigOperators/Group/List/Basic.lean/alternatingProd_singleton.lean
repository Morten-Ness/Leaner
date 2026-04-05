import Mathlib

variable {ι α β M N P G : Type*}

variable [One G] [Mul G] [Inv G]

theorem alternatingProd_singleton (a : G) : alternatingProd [a] = a := rfl

