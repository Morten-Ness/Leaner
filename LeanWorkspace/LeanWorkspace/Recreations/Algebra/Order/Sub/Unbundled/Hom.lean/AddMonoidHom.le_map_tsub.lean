import Mathlib

variable {α β : Type*}

variable [Preorder α]

variable [AddCommMonoid α] [Sub α] [OrderedSub α]

theorem AddMonoidHom.le_map_tsub [Preorder β] [AddZeroClass β] [Sub β] [OrderedSub β] (f : α →+ β)
    (hf : Monotone f) (a b : α) : f a - f b ≤ f (a - b) := f.toAddHom.le_map_tsub hf a b

