import Mathlib

variable {R : Type*}

theorem IsSumSq.sum_sq [CommSemiring R] {ι : Type*} (I : Finset ι) (a : ι → R) :
    IsSumSq (∑ i ∈ I, a i ^ 2) := by aesop

