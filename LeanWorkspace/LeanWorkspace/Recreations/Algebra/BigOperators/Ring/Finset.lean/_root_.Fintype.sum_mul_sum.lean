import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [NonUnitalNonAssocSemiring R]

theorem Finset.sum_mul_sum _root_.Fintype [Fintype ι] [Fintype κ] (f : ι → R) (g : κ → R) :
    (∑ i, f i) * ∑ j, g j = ∑ i, ∑ j, f i * g j := Finset.sum_mul_sum _ _ _ _

