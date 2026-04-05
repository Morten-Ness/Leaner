import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [CommSemiring R]

theorem sum_pow_mul_eq_add_pow (a b : R) (s : Finset ι) :
    (∑ t ∈ s.powerset, a ^ #t * b ^ (#s - #t)) = (a + b) ^ #s := by
  classical
  rw [← prod_const, Finset.prod_add]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [prod_const, prod_const, ← card_sdiff_of_subset (mem_powerset.1 ht)]

