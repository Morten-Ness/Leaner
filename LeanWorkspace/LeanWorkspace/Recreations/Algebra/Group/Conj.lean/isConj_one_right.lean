import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α] [Monoid β]

theorem isConj_one_right {a : α} : IsConj 1 a ↔ a = 1 := by
  refine ⟨fun ⟨c, h⟩ => ?_, fun h => by rw [h]⟩
  rw [SemiconjBy, mul_one] at h
  exact c.isUnit.mul_eq_right.mp h.symm

