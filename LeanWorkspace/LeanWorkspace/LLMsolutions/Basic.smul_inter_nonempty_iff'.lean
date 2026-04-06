import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

theorem smul_inter_nonempty_iff' {s t : Set α} {x : α} :
    (x • s ∩ t).Nonempty ↔ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a / b = x := by
  constructor
  · rintro ⟨y, ⟨hyxs, hyt⟩⟩
    rcases hyxs with ⟨b, hbs, rfl⟩
    refine ⟨x * b, b, ?_, ?_⟩
    · exact ⟨hyt, hbs⟩
    · simp [div_eq_mul_inv, mul_assoc]
  · rintro ⟨a, b, ⟨hat, hbs⟩, habx⟩
    refine ⟨a, ?_⟩
    refine ⟨?_, hat⟩
    refine ⟨b, hbs, ?_⟩
    rw [← habx]
    simp [div_eq_mul_inv, mul_assoc]
