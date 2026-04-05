import Mathlib

variable {ι α β M N P G : Type*}

theorem alternatingProd_cons_cons [DivInvMonoid G] (a b : G) (l : List G) :
    alternatingProd (a :: b :: l) = a / b * alternatingProd l := by
  rw [div_eq_mul_inv, List.alternatingProd_cons_cons']

