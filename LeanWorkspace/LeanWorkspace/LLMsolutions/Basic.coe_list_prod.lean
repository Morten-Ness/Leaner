import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

theorem coe_list_prod (s : List (Finset α)) : (↑s.prod : Set α) = (s.map (↑)).prod := by
  induction s with
  | nil =>
      ext x
      simp
  | cons a s ih =>
      ext x
      simp [ih, mul_assoc]
