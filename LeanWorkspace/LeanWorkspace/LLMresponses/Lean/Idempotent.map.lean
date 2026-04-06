import Mathlib

variable {M N S : Type*}

theorem map {M N F} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N] {e : M}
    (he : IsIdempotentElem e) (f : F) : IsIdempotentElem (f e) := by
  dsimp [IsIdempotentElem] at he ⊢
  calc
    f e * f e = f (e * e) := by rw [map_mul]
    _ = f e := by rw [he]
