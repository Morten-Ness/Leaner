import Mathlib

variable {R : Type*}

theorem IsSumSq.sum_isSquare [AddCommMonoid R] [Mul R] {ι : Type*} (I : Finset ι) {x : ι → R}
    (hx : ∀ i ∈ I, IsSquare <| x i) : IsSumSq (∑ i ∈ I, x i) := by aesop

