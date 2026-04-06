import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem map_modEq_iff {N F : Type*} [AddCommMonoid N] [FunLike F M N] [AddMonoidHomClass F M N]
    (f : F) (hf : Function.Injective f) : f a ≡ f b [PMOD f p] ↔ a ≡ b [PMOD p] := by
  constructor
  · rintro ⟨m, n, h⟩
    refine ⟨m, n, ?_⟩
    apply hf
    simpa using h
  · rintro ⟨m, n, h⟩
    refine ⟨m, n, ?_⟩
    simpa using congrArg f h
