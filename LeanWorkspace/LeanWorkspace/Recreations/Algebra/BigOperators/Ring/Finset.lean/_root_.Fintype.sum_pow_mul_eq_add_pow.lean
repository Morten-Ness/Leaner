import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [CommSemiring R]

theorem Finset.sum_pow_mul_eq_add_pow _root_.Fintype (ι : Type*) [Fintype ι] (a b : R) :
    ∑ s : Finset ι, a ^ #s * b ^ (Fintype.card ι - #s) = (a + b) ^ Fintype.card ι := Finset.sum_pow_mul_eq_add_pow _ _ _

