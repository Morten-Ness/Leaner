import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [FunLike F M₀ M₀']

theorem map_ne_zero_of_mem_nonZeroDivisors [Nontrivial M₀] [ZeroHomClass F M₀ M₀'] (g : F)
    (hg : Function.Injective (g : M₀ → M₀')) {x : M₀} (h : x ∈ M₀⁰) : g x ≠ 0 := fun h0 ↦
  one_ne_zero (h.2 1 ((one_mul x).symm ▸ hg (h0.trans (map_zero g).symm)))

