import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

theorem mul_univ_of_one_mem [Fintype α] (hs : (1 : α) ∈ s) : s * univ = univ := eq_univ_iff_forall.2 fun _ => Finset.mem_mul.2 ⟨_, hs, _, mem_univ _, one_mul _⟩

