import Mathlib

variable {ι : Sort*} {M α : Type*}

theorem smul_strictMono_right [SMul M α] [Preorder α] [CovariantClass M α HSMul.hSMul LT.lt]
    (m : M) : StrictMono (HSMul.hSMul m : α → α) := fun _ _ => CovariantClass.elim _

