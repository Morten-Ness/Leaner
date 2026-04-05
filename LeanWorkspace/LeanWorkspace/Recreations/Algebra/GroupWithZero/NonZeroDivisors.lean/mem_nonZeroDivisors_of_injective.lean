import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [FunLike F M₀ M₀']

theorem mem_nonZeroDivisors_of_injective [MonoidWithZeroHomClass F M₀ M₀'] {f : F}
    (hf : Function.Injective f) (hx : f x ∈ M₀'⁰) : x ∈ M₀⁰ := ⟨fun y hy ↦ hf <| map_zero f ▸ hx.1 (f y) (map_mul f x y ▸ map_zero f ▸ congrArg f hy),
    fun y hy ↦ hf <| map_zero f ▸ hx.2 (f y) (map_mul f y x ▸ map_zero f ▸ congrArg f hy)⟩

