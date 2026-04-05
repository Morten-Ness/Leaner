import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.add_nsmul_eq [AddMonoid α] [SubtractionMonoid β] (h : Function.Antiperiodic f c)
    (n : ℕ) : f (x + n • c) = (-1) ^ n • f x := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [h.even_nsmul_periodic]
    simp
  · rw [h.odd_nsmul_antiperiodic]
    simp [pow_add]

