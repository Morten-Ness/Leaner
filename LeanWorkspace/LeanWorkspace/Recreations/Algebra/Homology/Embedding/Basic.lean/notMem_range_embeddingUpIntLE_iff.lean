import Mathlib

variable {ι ι' : Type*} (c : ComplexShape ι) (c' : ComplexShape ι')

variable (p : ℤ)

theorem notMem_range_embeddingUpIntLE_iff (n : ℤ) :
    (∀ (i : ℕ), (ComplexShape.embeddingUpIntLE p).f i ≠ n) ↔ p < n := by
  constructor
  · intro h
    by_contra
    exact h (p - n).natAbs (by simp; lia)
  · intros
    dsimp
    lia

