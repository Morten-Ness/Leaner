import Mathlib

variable {R : Type*}

theorem IsSumSq.sum_mul_self [AddCommMonoid R] [Mul R] {ι : Type*} (I : Finset ι) (a : ι → R) :
    IsSumSq (∑ i ∈ I, a i * a i) := by aesop

