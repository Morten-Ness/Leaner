import Mathlib

variable (α β : Type*) [Monoid α] [PartialOrder α] [Monoid β] [Preorder β]

theorem snd_comp_inr : (OrderMonoidHom.snd α β).comp (OrderMonoidHom.inr α β) = .id β := rfl

