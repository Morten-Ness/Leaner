import Mathlib

variable {R S G M N O ι : Type*}

variable [CommSemiring R]

variable [CommMonoid M]

theorem prod_single (s : Finset ι) (m : ι → M) (r : ι → R) :
    ∏ i ∈ s, single (m i) (r i) = single (∏ i ∈ s, m i) (∏ i ∈ s, r i) := Finset.cons_induction_on s rfl fun i s hi ih ↦ by
    rw [prod_cons, ih, MonoidAlgebra.single_mul_single, prod_cons, prod_cons]

