import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [FunLike F M₀ M₀']

theorem nonZeroDivisors_le_comap_nonZeroDivisors_of_injective [NoZeroDivisors M₀']
    [MonoidWithZeroHomClass F M₀ M₀'] (f : F) (hf : Function.Injective f) : M₀⁰ ≤ M₀'⁰.comap f := Submonoid.le_comap_of_map_le _ (map_le_nonZeroDivisors_of_injective _ hf le_rfl)

