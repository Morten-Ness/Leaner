import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable [DecidableEq ι]

theorem of_smul (i : ι) (c : R) (x) : of M i (c • x) = c • of M i x := (DirectSum.lof R ι M i).map_smul c x

