import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem map {N F : Type*} [AddCommMonoid N] [FunLike F M N] [AddMonoidHomClass F M N]
    (f : F) (h : a ≡ b [PMOD p]) : f a ≡ f b [PMOD f p] := by
  rw [AddCommGroup.modEq_iff_nsmul] at *
  rcases h with ⟨m, n, h⟩
  use m, n
  simpa using congr(f $h)

