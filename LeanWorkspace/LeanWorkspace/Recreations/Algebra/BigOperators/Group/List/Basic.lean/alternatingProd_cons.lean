import Mathlib

variable {ι α β M N P G : Type*}

variable [CommGroup G]

theorem alternatingProd_cons (a : G) (l : List G) :
    alternatingProd (a :: l) = a / alternatingProd l := by
  rw [div_eq_mul_inv, List.alternatingProd_cons']

