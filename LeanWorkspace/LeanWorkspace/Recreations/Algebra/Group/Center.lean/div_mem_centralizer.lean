import Mathlib

variable {M : Type*} {S T : Set M}

variable [Group M] {a b : M}

theorem div_mem_centralizer (ha : a ∈ Set.centralizer S) (hb : b ∈ Set.centralizer S) :
    a / b ∈ Set.centralizer S := by
  simpa only [div_eq_mul_inv] using Set.mul_mem_centralizer ha (Set.inv_mem_centralizer hb)

