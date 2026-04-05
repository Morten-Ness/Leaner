import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [FunLike F M₀ M₀']

theorem map_mem_nonZeroDivisors [Nontrivial M₀] [NoZeroDivisors M₀'] [ZeroHomClass F M₀ M₀'] (g : F)
    (hg : Function.Injective g) {x : M₀} (h : x ∈ M₀⁰) : g x ∈ M₀'⁰ := ⟨fun _ ↦ eq_zero_of_ne_zero_of_mul_left_eq_zero (map_ne_zero_of_mem_nonZeroDivisors g hg h),
    fun _ ↦ eq_zero_of_ne_zero_of_mul_right_eq_zero (map_ne_zero_of_mem_nonZeroDivisors g hg h)⟩

