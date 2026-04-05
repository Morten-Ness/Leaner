import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem mul_mem_nonZeroDivisorsLeft_of_mem_nonZeroDivisorsLeft (hx : x ∈ nonZeroDivisorsLeft M₀)
    (hy : y ∈ nonZeroDivisorsLeft M₀) :
    x * y ∈ nonZeroDivisorsLeft M₀ := Submonoid.mul_mem _ hx hy

