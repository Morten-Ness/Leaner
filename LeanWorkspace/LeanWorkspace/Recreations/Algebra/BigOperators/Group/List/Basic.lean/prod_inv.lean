import Mathlib

variable {ι α β M N P G : Type*}

variable [CommGroup G]

theorem prod_inv {K : Type*} [DivisionCommMonoid K] :
    ∀ L : List K, L.prod⁻¹ = (L.map fun x => x⁻¹).prod
  | [] => by simp
  | x :: xs => by simp [mul_comm, prod_inv xs]
