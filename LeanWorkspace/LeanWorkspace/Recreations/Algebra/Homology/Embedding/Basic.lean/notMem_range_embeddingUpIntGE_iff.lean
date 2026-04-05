import Mathlib

variable {ι ι' : Type*} (c : ComplexShape ι) (c' : ComplexShape ι')

variable (p : ℤ)

theorem notMem_range_embeddingUpIntGE_iff (n : ℤ) :
    (∀ (i : ℕ), (ComplexShape.embeddingUpIntGE p).f i ≠ n) ↔ n < p := by
  constructor
  · intro h
    by_contra
    exact h (n - p).natAbs (by simp; lia)
  · intros
    dsimp
    lia

