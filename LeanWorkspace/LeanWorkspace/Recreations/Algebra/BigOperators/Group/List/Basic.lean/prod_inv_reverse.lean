import Mathlib

variable {ι α β M N P G : Type*}

variable [Group G]

theorem prod_inv_reverse : ∀ L : List G, L.prod⁻¹ = (L.map fun x => x⁻¹).reverse.prod
  | [] => by simp
  | x :: xs => by simp [prod_append, prod_inv_reverse xs]
