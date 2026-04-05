import Mathlib

variable {α} {R : Type v}

theorem isSMulRegular_iff [SMul α R] {r : α} :
    IsSMulRegular (ULift R) r ↔ IsSMulRegular R r := Equiv.ulift.symm.comp_injective _ |>.trans <| Equiv.ulift.symm.injective_comp _ |>.symm

