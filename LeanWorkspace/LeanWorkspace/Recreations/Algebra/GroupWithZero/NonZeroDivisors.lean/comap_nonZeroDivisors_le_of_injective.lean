import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [FunLike F M₀ M₀']

theorem comap_nonZeroDivisors_le_of_injective [MonoidWithZeroHomClass F M₀ M₀'] {f : F}
    (hf : Function.Injective f) : M₀'⁰.comap f ≤ M₀⁰ := fun _ ha ↦ mem_nonZeroDivisors_of_injective hf (Submonoid.mem_comap.mp ha)

