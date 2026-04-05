import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem exists_list_of_mem_closure {s : Set M} {x : M} (hx : x ∈ closure s) :
    ∃ l : List M, (∀ y ∈ l, y ∈ s) ∧ l.prod = x := by
  rwa [← SetLike.mem_coe, Submonoid.closure_eq_image_prod, Set.mem_image] at hx

