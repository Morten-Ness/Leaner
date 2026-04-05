import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem list_prod_mem {l : List G} : (∀ x ∈ l, x ∈ K) → l.prod ∈ K := list_prod_mem

