import Mathlib

open scoped DirectSum

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

theorem coeFnLinearMap_apply (v : ⨁ i, M i) : DirectSum.coeFnLinearMap R v = v := rfl

