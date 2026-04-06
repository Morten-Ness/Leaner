import Mathlib

open scoped DirectSum

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

theorem apply_eq_component (f : ⨁ i, M i) (i : ι) : f i = DirectSum.component R ι M i f := rfl
