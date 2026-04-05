import Mathlib

variable {α : Type u}

theorem IsUnit.nonempty_invertible [Monoid α] {a : α} (h : IsUnit a) : Nonempty (Invertible a) := let ⟨x, hx⟩ := h
  ⟨x.invertible.copy _ hx.symm⟩

