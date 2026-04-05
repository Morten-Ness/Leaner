import Mathlib

variable {R S M N : Type*}

variable [Semiring R] [Semiring S]

variable [AddCommMonoid M] [Module R M] [Module S M] [AddCommMonoid N] [Module R N]
  {r : R} {m m₁ m₂ : M}

theorem Module.IsTorsionFree.comap [IsTorsionFree S M] (f : R → S)
    (isRegular : ∀ r, IsRegular r → IsRegular (f r)) (smul : ∀ (r : R) (m : M), f r • m = r • m) :
    IsTorsionFree R M where
  isSMulRegular r hr := (isRegular _ hr).isSMulRegular.of_map f (smul r)

