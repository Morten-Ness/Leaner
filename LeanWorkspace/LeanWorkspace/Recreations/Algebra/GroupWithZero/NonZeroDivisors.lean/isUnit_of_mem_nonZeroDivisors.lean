import Mathlib

variable {G₀ : Type*} [GroupWithZero G₀] {x : G₀}

theorem isUnit_of_mem_nonZeroDivisors (hx : x ∈ nonZeroDivisors G₀) : IsUnit x := (nonZeroDivisorsEquivUnits ⟨x, hx⟩).isUnit

