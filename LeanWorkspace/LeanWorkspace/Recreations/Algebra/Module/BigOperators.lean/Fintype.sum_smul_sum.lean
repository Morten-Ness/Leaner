import Mathlib

variable {ι κ α β R M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

theorem Fintype.sum_smul_sum [Fintype α] [Fintype β] (f : α → R) (g : β → M) :
    (∑ i, f i) • ∑ j, g j = ∑ i, ∑ j, f i • g j := Finset.sum_smul_sum _ _

