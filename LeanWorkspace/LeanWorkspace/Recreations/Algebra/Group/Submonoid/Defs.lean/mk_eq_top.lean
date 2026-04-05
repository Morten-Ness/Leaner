import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

variable {S : Submonoid M}

theorem mk_eq_top (toSubsemigroup : Subsemigroup M) (one_mem') :
    Submonoid.mk toSubsemigroup one_mem' = ⊤ ↔ toSubsemigroup = ⊤ := by simp [← SetLike.coe_set_eq]

