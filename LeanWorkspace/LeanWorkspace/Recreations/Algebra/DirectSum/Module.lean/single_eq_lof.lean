import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable [DecidableEq ι]

theorem single_eq_lof (i : ι) (b : M i) : DFinsupp.single i b = DirectSum.lof R ι M i b := rfl

