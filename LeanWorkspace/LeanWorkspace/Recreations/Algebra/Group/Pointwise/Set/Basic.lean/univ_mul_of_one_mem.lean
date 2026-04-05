import Mathlib

variable {F α β γ : Type*}

variable [Monoid α] {s t : Set α} {a : α} {m n : ℕ}

theorem univ_mul_of_one_mem (ht : (1 : α) ∈ t) : univ * t = univ := eq_univ_iff_forall.2 fun _ => Set.mem_mul.2 ⟨_, mem_univ _, _, ht, mul_one _⟩

