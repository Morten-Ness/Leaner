import Mathlib

variable {F α β γ : Type*}

variable [Monoid α] {s t : Set α} {a : α} {m n : ℕ}

theorem mul_univ_of_one_mem (hs : (1 : α) ∈ s) : s * univ = univ := eq_univ_iff_forall.2 fun _ => Set.mem_mul.2 ⟨_, hs, _, mem_univ _, one_mul _⟩

