import Mathlib

open scoped DirectSum

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

theorem linearEquivFunOnFintype_symm_coe [Fintype ι] (f : ⨁ i, M i) :
    (DirectSum.linearEquivFunOnFintype R ι M).symm f = f := by
  exact (DirectSum.linearEquivFunOnFintype R ι M).left_inv f
