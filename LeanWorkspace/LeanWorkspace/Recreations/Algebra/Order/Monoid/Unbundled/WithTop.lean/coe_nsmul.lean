import Mathlib

variable {α : Type u} {β : Type v}

variable [AddMonoid α]

theorem coe_nsmul (a : α) (n : ℕ) : ↑(n • a) = n • (a : WithBot α) := (WithBot.addHom : α →+ WithBot α).map_nsmul _ _

