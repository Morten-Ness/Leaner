import Mathlib

variable {M G α β : Type*}

theorem MulAction.IsPretransitive.of_isScalarTower (M : Type*) {N α : Type*} [Monoid N] [SMul M N]
    [MulAction N α] [SMul M α] [IsScalarTower M N α] [IsPretransitive M α] : IsPretransitive N α := of_smul_eq (fun x : M ↦ x • 1) (smul_one_smul N _ _)

