import Mathlib

variable {M : Type*} {S T : Set M}

variable [DivisionMonoid M] {a b : M}

theorem div_mem_center (ha : a ∈ Set.center M) (hb : b ∈ Set.center M) : a / b ∈ Set.center M := by
  rw [div_eq_mul_inv]
  exact Set.mul_mem_center ha (Set.inv_mem_center hb)

