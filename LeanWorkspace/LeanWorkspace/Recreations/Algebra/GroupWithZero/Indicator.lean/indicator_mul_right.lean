import Mathlib

variable {ι κ G₀ M₀ R : Type*}

variable [MulZeroClass M₀] {s t : Set ι} {i : ι}

theorem indicator_mul_right (s : Set ι) (f g : ι → M₀) :
    indicator s (fun j ↦ f j * g j) i = f i * indicator s g i := by
  simp only [indicator]
  split_ifs
  · rfl
  · rw [mul_zero]

