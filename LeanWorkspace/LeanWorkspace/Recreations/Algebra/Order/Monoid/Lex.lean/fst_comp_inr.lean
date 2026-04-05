import Mathlib

variable (α β : Type*) [Monoid α] [PartialOrder α] [Monoid β] [Preorder β]

theorem fst_comp_inr : (OrderMonoidHom.fst α β).comp (OrderMonoidHom.inr α β) = 1 := rfl

