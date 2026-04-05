import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem map_modEq_iff {N F : Type*} [AddCommMonoid N] [FunLike F M N] [AddMonoidHomClass F M N]
    (f : F) (hf : Function.Injective f) : f a ≡ f b [PMOD f p] ↔ a ≡ b [PMOD p] := by
  simp only [AddCommGroup.modEq_iff_nsmul, ← map_nsmul, ← map_add, hf.eq_iff]

