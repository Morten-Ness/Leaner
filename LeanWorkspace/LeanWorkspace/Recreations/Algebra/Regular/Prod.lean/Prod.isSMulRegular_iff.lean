import Mathlib

variable {α R S : Type*}

theorem Prod.isSMulRegular_iff [SMul α R] [SMul α S] {r : α} [Nonempty R] [Nonempty S] :
    IsSMulRegular (R × S) r ↔ IsSMulRegular R r ∧ IsSMulRegular S r := Prod.map_injective

