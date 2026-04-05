import Mathlib

variable {α β M N : Type*}

variable [MulOneClass M] {s t : Set α} {a : α}

theorem mulIndicator_self_mul_compl_apply (s : Set α) (f : α → M) (a : α) :
    mulIndicator s f a * mulIndicator sᶜ f a = f a := by _cases (fun ha : a ∈ s => by simp [ha]) fun ha => by simp [ha]

