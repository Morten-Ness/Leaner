import Mathlib

variable {M G α β : Type*}

variable (M) [SMul M α] [IsPretransitive M α]

theorem surjective_smul (x : α) : Function.Surjective fun c : M ↦ c • x := MulAction.exists_smul_eq M x

