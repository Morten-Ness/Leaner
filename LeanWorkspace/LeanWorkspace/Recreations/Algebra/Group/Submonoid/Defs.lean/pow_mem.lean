import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

theorem pow_mem {M A} [Monoid M] [SetLike A M] [SubmonoidClass A M] {S : A} {x : M}
    (hx : x ∈ S) : ∀ n : ℕ, x ^ n ∈ S
  | 0 => by
    rw [pow_zero]
    exact OneMemClass.one_mem S
  | n + 1 => by
    rw [pow_succ]
    exact mul_mem (pow_mem hx n) hx
