import Mathlib

variable (α β : Type*) [Monoid α] [PartialOrder α] [Monoid β] [Preorder β]

theorem fst_comp_inl : (OrderMonoidHom.fst α β).comp (OrderMonoidHom.inl α β) = .id α := rfl

