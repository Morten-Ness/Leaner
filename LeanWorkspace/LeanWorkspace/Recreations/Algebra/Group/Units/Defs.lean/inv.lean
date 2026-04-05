import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [DivisionMonoid α] {a b c : α}

theorem inv (h : IsUnit a) : IsUnit a⁻¹ := by
  obtain ⟨u, hu⟩ := h
  rw [← hu, ← Units.val_inv_eq_inv_val]
  exact Units.isUnit _

