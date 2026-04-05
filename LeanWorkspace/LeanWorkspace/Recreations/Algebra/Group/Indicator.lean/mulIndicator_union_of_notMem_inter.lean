import Mathlib

variable {α β M N : Type*}

variable [MulOneClass M] {s t : Set α} {a : α}

theorem mulIndicator_union_of_notMem_inter (h : a ∉ s ∩ t) (f : α → M) :
    mulIndicator (s ∪ t) f a = mulIndicator s f a * mulIndicator t f a := by
  rw [← Set.mulIndicator_union_mul_inter_apply f s t, mulIndicator_of_notMem h, mul_one]

