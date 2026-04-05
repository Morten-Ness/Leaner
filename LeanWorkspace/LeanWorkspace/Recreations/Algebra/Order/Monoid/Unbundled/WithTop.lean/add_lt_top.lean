import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithTop α} {a b : α}

theorem add_lt_top [LT α] : x + y < ⊤ ↔ x < ⊤ ∧ y < ⊤ := by
  simp_rw [WithTop.lt_top_iff_ne_top, WithTop.add_ne_top]

