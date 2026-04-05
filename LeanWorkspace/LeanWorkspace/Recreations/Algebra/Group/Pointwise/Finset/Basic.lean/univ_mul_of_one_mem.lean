import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

theorem univ_mul_of_one_mem [Fintype α] (ht : (1 : α) ∈ t) : univ * t = univ := eq_univ_iff_forall.2 fun _ => Finset.mem_mul.2 ⟨_, mem_univ _, _, ht, mul_one _⟩

