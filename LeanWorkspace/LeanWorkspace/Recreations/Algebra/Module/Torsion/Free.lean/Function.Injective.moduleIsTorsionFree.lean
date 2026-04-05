import Mathlib

variable {R S M N : Type*}

variable [Semiring R] [Semiring S]

variable [AddCommMonoid M] [Module R M] [Module S M] [AddCommMonoid N] [Module R N]
  {r : R} {m m₁ m₂ : M}

theorem Function.Injective.moduleIsTorsionFree [IsTorsionFree R N] (f : M → N) (hf : f.Injective)
    (smul : ∀ (r : R) (m : M), f (r • m) = r • f m) : IsTorsionFree R M where
  isSMulRegular r hr m₁ m₂ hm := hf <| hr.isSMulRegular <| by simpa [smul] using congr(f $hm)

