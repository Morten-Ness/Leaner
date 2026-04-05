import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable (g : L →+* M) (f : K →+* L)

theorem mem_fieldRange_self (x : K) : f x ∈ f.fieldRange := exists_apply_eq_apply _ _

