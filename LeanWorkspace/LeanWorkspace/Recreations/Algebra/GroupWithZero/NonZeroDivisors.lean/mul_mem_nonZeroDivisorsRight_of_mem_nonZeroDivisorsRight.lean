import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem mul_mem_nonZeroDivisorsRight_of_mem_nonZeroDivisorsRight (hx : x ∈ nonZeroDivisorsRight M₀)
    (hy : y ∈ nonZeroDivisorsRight M₀) :
    x * y ∈ nonZeroDivisorsRight M₀ := Submonoid.mul_mem _ hx hy

