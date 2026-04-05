import Mathlib

variable {M : Type*} [AddCancelCommMonoid M] [AddMonoid.FG M] [IsAddTorsionFree M]

theorem embedding_injective : Function.Injective (AffineAddMonoid.embedding M) := by
  simpa [AffineAddMonoid.embedding] using mk_left_injective 0

