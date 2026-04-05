import Mathlib

variable {ι α β M N P G : Type*}

variable [CommGroup G]

theorem alternatingProd_cons' :
    ∀ (a : G) (l : List G), alternatingProd (a :: l) = a * (alternatingProd l)⁻¹
  | a, [] => by rw [List.alternatingProd_nil, inv_one, mul_one, List.alternatingProd_singleton]
  | a, b :: l => by
    rw [List.alternatingProd_cons_cons', alternatingProd_cons' b l, mul_inv, inv_inv, mul_assoc]
