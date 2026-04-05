import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

theorem component.lof_self [DecidableEq ι] (i : ι) (b : M i) :
    DirectSum.component R ι M i ((DirectSum.lof R ι M i) b) = b := DirectSum.lof_apply R i b

