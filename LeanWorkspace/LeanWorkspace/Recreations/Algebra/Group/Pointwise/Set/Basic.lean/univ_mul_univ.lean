import Mathlib

variable {F α β γ : Type*}

variable [Monoid α] {s t : Set α} {a : α} {m n : ℕ}

theorem univ_mul_univ : (univ : Set α) * univ = univ := Set.mul_univ_of_one_mem <| mem_univ _

