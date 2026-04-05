import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

theorem univ_mul_univ [Fintype α] : (univ : Finset α) * univ = univ := Finset.mul_univ_of_one_mem <| mem_univ _

