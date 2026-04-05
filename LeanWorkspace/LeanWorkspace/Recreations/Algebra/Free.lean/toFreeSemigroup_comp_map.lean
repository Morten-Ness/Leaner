import Mathlib

variable {α : Type u} {β : Type v}

theorem toFreeSemigroup_comp_map (f : α → β) :
    FreeMagma.toFreeSemigroup.comp (FreeMagma.map f) = (FreeSemigroup.map f).comp FreeMagma.toFreeSemigroup := by ext1; rfl

