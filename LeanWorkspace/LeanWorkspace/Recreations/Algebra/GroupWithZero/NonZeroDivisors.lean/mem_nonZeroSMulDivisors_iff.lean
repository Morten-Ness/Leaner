import Mathlib

variable {M₀ M : Type*} [MonoidWithZero M₀] [Zero M] [MulAction M₀ M] {x : M₀}

theorem mem_nonZeroSMulDivisors_iff : x ∈ M₀⁰[M] ↔ ∀ (m : M), x • m = 0 → m = 0 := Iff.rfl

