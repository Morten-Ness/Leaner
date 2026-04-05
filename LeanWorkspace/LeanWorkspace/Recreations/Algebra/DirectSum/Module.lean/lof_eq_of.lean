import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable [DecidableEq ι]

theorem lof_eq_of (i : ι) (b : M i) : DirectSum.lof R ι M i b = of M i b := rfl

