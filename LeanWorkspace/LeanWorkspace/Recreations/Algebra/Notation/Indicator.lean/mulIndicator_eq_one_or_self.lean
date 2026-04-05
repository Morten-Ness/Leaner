import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_eq_one_or_self (s : Set α) (f : α → M) (a : α) :
    Set.mulIndicator s f a = 1 ∨ Set.mulIndicator s f a = f a := by
  by_cases h : a ∈ s
  · exact Or.inr (Set.mulIndicator_of_mem h f)
  · exact Or.inl (Set.mulIndicator_of_notMem h f)

