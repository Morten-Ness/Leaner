import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_mem_eq_one_of_forall_eq_one {f : α → M} {s : Set α} (h : ∀ x ∈ s, f x = 1) :
    ∏ᶠ i ∈ s, f i = 1 := by simp +contextual [h]

