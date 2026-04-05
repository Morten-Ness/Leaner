import Mathlib

variable {α : Type u} {β : Type v}

theorem toFreeSemigroup_comp_of : @FreeMagma.toFreeSemigroup α ∘ Magma.AssocQuotient.of = FreeSemigroup.of := rfl

