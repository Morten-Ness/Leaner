import Mathlib

variable {α β M N : Type*}

theorem map_mulIndicator {M N F : Type*} [One M] [One N] [FunLike F M N] [OneHomClass F M N] (f : F)
    (s : Set α) (g : α → M) (x : α) : f (s.mulIndicator g x) = s.mulIndicator (f ∘ g) x := by
  simp [Set.mulIndicator_comp_of_one]

