import Mathlib

variable {α : Type u} {β : Type v}

theorem toFreeSemigroup_of (x : α) : FreeMagma.toFreeSemigroup (Magma.AssocQuotient.of x) = FreeSemigroup.of x := rfl

