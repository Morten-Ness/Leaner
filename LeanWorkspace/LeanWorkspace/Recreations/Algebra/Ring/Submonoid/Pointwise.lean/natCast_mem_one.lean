import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [AddMonoidWithOne R]

theorem natCast_mem_one (n : ℕ) : (n : R) ∈ (1 : AddSubmonoid R) := ⟨_, rfl⟩

