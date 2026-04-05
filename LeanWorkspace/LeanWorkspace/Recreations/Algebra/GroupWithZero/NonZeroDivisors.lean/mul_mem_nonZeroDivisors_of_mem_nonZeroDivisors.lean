import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem mul_mem_nonZeroDivisors_of_mem_nonZeroDivisors (hx : x ∈ M₀⁰) (hy : y ∈ M₀⁰) :
    x * y ∈ M₀⁰ := mem_nonZeroDivisors_iff'.mpr ⟨Submonoid.mul_mem _ hx.1 hy.1, Submonoid.mul_mem _ hx.2 hy.2⟩

