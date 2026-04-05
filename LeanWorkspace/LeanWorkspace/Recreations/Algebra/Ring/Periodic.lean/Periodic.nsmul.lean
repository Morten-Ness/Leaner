import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.nsmul [AddMonoid α] (h : Function.Periodic f c) (n : ℕ) : Function.Periodic f (n • c) := by
  induction n <;> simp_all [add_nsmul, ← add_assoc]

