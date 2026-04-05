import Mathlib

variable {ι α β M N P G : Type*}

variable [One G] [Mul G] [Inv G]

theorem alternatingProd_nil : alternatingProd ([] : List G) = 1 := rfl

