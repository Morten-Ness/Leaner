import Mathlib

variable {M N S : Type*}

theorem map {M N F} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N] {e : M}
    (he : IsIdempotentElem e) (f : F) : IsIdempotentElem (f e) := by
  rw [IsIdempotentElem, ← map_mul, IsIdempotentElem.eq he]

