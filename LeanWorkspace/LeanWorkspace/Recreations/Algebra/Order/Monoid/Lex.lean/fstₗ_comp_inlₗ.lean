import Mathlib

variable (α β : Type*) [Monoid α] [PartialOrder α] [Monoid β] [Preorder β]

theorem fstₗ_comp_inlₗ : (OrderMonoidHom.fstₗ α β).comp (OrderMonoidHom.inlₗ α β) = .id α := rfl

