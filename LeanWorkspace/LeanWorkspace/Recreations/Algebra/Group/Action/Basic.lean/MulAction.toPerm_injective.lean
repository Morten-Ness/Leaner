import Mathlib

variable {G M A B α β : Type*}

variable [Group α] [MulAction α β]

theorem MulAction.toPerm_injective [FaithfulSMul α β] :
    Function.Injective (MulAction.toPerm : α → Equiv.Perm β) := (show Function.Injective (Equiv.toFun ∘ MulAction.toPerm) from smul_left_injective').of_comp

