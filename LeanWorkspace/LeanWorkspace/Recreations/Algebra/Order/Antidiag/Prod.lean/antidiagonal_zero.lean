import Mathlib

variable {A : Type*}

variable [AddCommMonoid A] [PartialOrder A] [CanonicallyOrderedAdd A] [HasAntidiagonal A]

theorem antidiagonal_zero : antidiagonal (0 : A) = {(0, 0)} := by
  ext ⟨x, y⟩
  simp

