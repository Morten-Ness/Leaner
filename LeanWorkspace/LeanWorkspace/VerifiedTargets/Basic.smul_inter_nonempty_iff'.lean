import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem smul_inter_nonempty_iff' {s t : Set α} {x : α} :
    (x • s ∩ t).Nonempty ↔ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a / b = x := by
  simp_rw [Set.smul_inter_nonempty_iff, div_eq_mul_inv]

