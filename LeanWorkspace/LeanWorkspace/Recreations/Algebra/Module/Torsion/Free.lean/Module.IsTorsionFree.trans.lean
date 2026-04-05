import Mathlib

variable {R S M N : Type*}

variable [Semiring R] [Semiring S]

variable [AddCommMonoid M] [Module R M] [Module S M] [AddCommMonoid N] [Module R N]
  {r : R} {m m₁ m₂ : M}

variable [IsTorsionFree R M]

theorem Module.IsTorsionFree.trans [Module S R] [IsTorsionFree S R] [IsScalarTower S R R]
    [SMulCommClass S R R] [IsScalarTower S R M] : IsTorsionFree S M where
  isSMulRegular s hs x y hxy := by
    refine (?_ : IsRegular (s • 1 : R)).isSMulRegular (by simpa using hxy)
    exact ⟨fun x y hxy ↦ hs.isSMulRegular <| by simpa using hxy,
      fun x y hxy ↦ hs.isSMulRegular <| by simpa using hxy⟩

