import Mathlib

variable (α β : Type*) [Monoid α] [PartialOrder α] [Monoid β] [Preorder β]

theorem snd_comp_inl : (OrderMonoidHom.snd α β).comp (OrderMonoidHom.inl α β) = 1 := rfl

