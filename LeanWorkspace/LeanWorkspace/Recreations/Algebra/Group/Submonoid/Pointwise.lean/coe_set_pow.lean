import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

theorem coe_set_pow [SetLike S M] [SubmonoidClass S M] :
    ∀ {n} (_ : n ≠ 0) (H : S), (H ^ n : Set M) = H
  | 1, _, H => by simp
  | n + 2, _, H => by rw [pow_succ, coe_set_pow n.succ_ne_zero, coe_mul_coe]
