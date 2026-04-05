import Mathlib

variable {F α β : Type*}

variable [Semiring α] [Semiring β] {a b : α} {m n : ℕ}

theorem Odd.map [FunLike F α β] [RingHomClass F α β] (f : F) : Odd a → Odd (f a) := by
  rintro ⟨a, rfl⟩; exact ⟨f a, by simp [two_mul]⟩

