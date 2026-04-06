import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem map {N F : Type*} [AddCommMonoid N] [FunLike F M N] [AddMonoidHomClass F M N]
    (f : F) (h : a ≡ b [PMOD p]) : f a ≡ f b [PMOD f p] := by
  rcases h with ⟨m, n, hmn⟩
  exact ⟨m, n, by simpa [map_add, map_nsmul] using congrArg f hmn⟩
