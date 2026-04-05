import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable {S : Subsemigroup M}

theorem mk_eq_top (carrier : Set M) (mul_mem') : Subsemigroup.mk carrier mul_mem' = ⊤ ↔ carrier = .univ := by
  simp [← SetLike.coe_set_eq]

