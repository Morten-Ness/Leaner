import Mathlib

variable {ι κ G₀ M₀ R : Type*}

variable [MulZeroClass M₀] {s t : Set ι} {i : ι}

theorem indicator_mul (s : Set ι) (f g : ι → M₀) :
    indicator s (fun i ↦ f i * g i) = fun i ↦ indicator s f i * indicator s g i := by
  funext
  simp only [indicator]
  split_ifs
  · rfl
  rw [mul_zero]

