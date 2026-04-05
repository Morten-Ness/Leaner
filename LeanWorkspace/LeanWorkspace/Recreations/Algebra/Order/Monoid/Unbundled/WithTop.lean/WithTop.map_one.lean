import Mathlib

variable {α : Type u} {β : Type v}

variable [One α] {a : α}

theorem map_one {β} (f : α → β) : (1 : WithTop α).map f = (f 1 : WithTop β) := rfl

