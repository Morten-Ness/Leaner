import Mathlib

variable {R : Type*}

theorem IsSumSq.sum [AddCommMonoid R] [Mul R] {ι : Type*} {I : Finset ι} {s : ι → R}
    (hs : ∀ i ∈ I, IsSumSq <| s i) : IsSumSq (∑ i ∈ I, s i) := by
  simpa using sum_mem (S := AddSubmonoid.sumSq _) hs

