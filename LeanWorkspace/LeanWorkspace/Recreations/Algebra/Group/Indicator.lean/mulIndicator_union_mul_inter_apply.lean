import Mathlib

variable {α β M N : Type*}

variable [MulOneClass M] {s t : Set α} {a : α}

theorem mulIndicator_union_mul_inter_apply (f : α → M) (s t : Set α) (a : α) :
    mulIndicator (s ∪ t) f a * mulIndicator (s ∩ t) f a
      = mulIndicator s f a * mulIndicator t f a := by
  by_cases hs : a ∈ s <;> by_cases ht : a ∈ t <;> simp [*]

