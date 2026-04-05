import Mathlib

variable {ι α β M N P G : Type*}

variable [One G] [Mul G] [Inv G]

theorem alternatingProd_cons_cons' (a b : G) (l : List G) :
    alternatingProd (a :: b :: l) = a * b⁻¹ * alternatingProd l := rfl

