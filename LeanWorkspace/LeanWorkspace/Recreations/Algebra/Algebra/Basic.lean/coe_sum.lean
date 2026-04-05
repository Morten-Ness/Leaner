import Mathlib

open scoped Algebra

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] {ι : Type*} {s : Finset ι}

theorem coe_sum (a : ι → R) : ↑(∑ i ∈ s, a i) = ∑ i ∈ s, (↑(a i) : A) := map_sum (algebraMap R A) a s

