import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [FunLike F M₀ M₀']

theorem map_le_nonZeroDivisors_of_injective [NoZeroDivisors M₀'] [MonoidWithZeroHomClass F M₀ M₀']
    (f : F) (hf : Function.Injective f) {S : Submonoid M₀} (hS : S ≤ M₀⁰) : S.map f ≤ M₀'⁰ := by
  cases subsingleton_or_nontrivial M₀
  · simp [Subsingleton.elim S ⊥]
  · refine le_nonZeroDivisors_of_noZeroDivisors ?_
    rintro ⟨x, hx, hx0⟩
    exact zero_notMem_nonZeroDivisors <| hS <| map_eq_zero_iff f hf |>.mp hx0 ▸ hx

