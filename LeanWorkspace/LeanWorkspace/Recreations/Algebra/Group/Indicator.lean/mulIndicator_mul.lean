import Mathlib

variable {α β M N : Type*}

variable [MulOneClass M] {s t : Set α} {a : α}

theorem mulIndicator_mul (s : Set α) (f g : α → M) :
    (mulIndicator s fun a => f a * g a) = fun a => mulIndicator s f a * mulIndicator s g a := by
  funext
  simp only [mulIndicator]
  split_ifs
  · rfl
  rw [mul_one]

