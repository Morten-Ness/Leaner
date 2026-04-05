import Mathlib

variable {F α β : Type*}

variable [Semiring α] [Semiring β] {a b : α} {m n : ℕ}

theorem isUnit_two_iff_forall_even : IsUnit (2 : α) ↔ ∀ a : α, Even a := by
  refine ⟨Even.of_isUnit_two, fun h => ?_⟩
  obtain ⟨a, ha⟩ := h 1
  rw [← two_mul, eq_comm] at ha
  exact ⟨⟨2, a, ha, .trans (Commute.ofNat_right _ _).eq ha⟩, rfl⟩

