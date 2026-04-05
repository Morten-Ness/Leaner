import Mathlib

variable {α β : Type*}

variable [DecidableEq α] {s : Multiset α}

theorem coe_countAddMonoidHom (a : α) : (Multiset.countAddMonoidHom a : Multiset α → ℕ) = count a := rfl

