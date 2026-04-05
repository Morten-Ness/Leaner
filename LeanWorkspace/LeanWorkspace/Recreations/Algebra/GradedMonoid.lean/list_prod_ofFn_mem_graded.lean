import Mathlib

variable {ι : Type*}

variable {R : Type*}

variable {S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι]

variable {A : ι → S} [SetLike.GradedMonoid A]

theorem list_prod_ofFn_mem_graded {n} (i : Fin n → ι) (r : Fin n → R) (h : ∀ j, r j ∈ A (i j)) :
    (List.ofFn r).prod ∈ A (List.ofFn i).sum := by
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  exact SetLike.list_prod_map_mem_graded _ _ _ fun _ _ => h _

