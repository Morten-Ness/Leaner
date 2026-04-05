import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithTop α} {a b : α}

theorem add_eq_coe :
    ∀ {a b : WithTop α} {c : α}, a + b = c ↔ ∃ a' b' : α, ↑a' = a ∧ ↑b' = b ∧ a' + b' = c
  | ⊤, b, c => by simp
  | some a, ⊤, c => by simp
  | some a, some b, c => by norm_cast; simp
