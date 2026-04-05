import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.zsmul_sub_eq [AddCommGroup α] [SubtractionMonoid β] (h : Function.Antiperiodic f c)
    (n : ℤ) : f (n • c - x) = (n.negOnePow : ℤ) • f (-x) := by
  rw [sub_eq_add_neg, add_comm]
  exact h.add_zsmul_eq n

