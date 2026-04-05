import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

theorem lof_apply [DecidableEq ι] (i : ι) (b : M i) : ((DirectSum.lof R ι M i) b) i = b := DFinsupp.single_eq_same

