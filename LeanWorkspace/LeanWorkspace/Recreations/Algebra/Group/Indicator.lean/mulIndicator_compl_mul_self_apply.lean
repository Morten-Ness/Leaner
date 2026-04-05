import Mathlib

variable {α β M N : Type*}

variable [MulOneClass M] {s t : Set α} {a : α}

theorem mulIndicator_compl_mul_self_apply (s : Set α) (f : α → M) (a : α) :
    mulIndicator sᶜ f a * mulIndicator s f a = f a := by _cases (fun ha : a ∈ s => by simp [ha]) fun ha => by simp [ha]

