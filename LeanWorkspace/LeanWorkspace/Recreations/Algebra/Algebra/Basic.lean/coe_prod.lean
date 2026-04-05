import Mathlib

open scoped Algebra

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] {ι : Type*} {s : Finset ι}

theorem coe_prod (a : ι → R) : (↑(∏ i ∈ s, a i : R) : A) = ∏ i ∈ s, (↑(a i) : A) := map_prod (algebraMap R A) a s

