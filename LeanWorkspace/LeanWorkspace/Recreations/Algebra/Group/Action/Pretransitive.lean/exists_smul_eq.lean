import Mathlib

variable {M G α β : Type*}

variable (M) [SMul M α] [IsPretransitive M α]

theorem exists_smul_eq (x y : α) : ∃ m : M, m • x = y := IsPretransitive.exists_smul_eq x y

