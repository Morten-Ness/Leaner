import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [CommRing R]

theorem prod_sub [DecidableEq ι] (f g : ι → R) (s : Finset ι) :
    ∏ i ∈ s, (f i - g i) = ∑ t ∈ s.powerset, (-1) ^ #t * (∏ i ∈ s \ t, f i) * ∏ i ∈ t, g i := by
  simp [sub_eq_neg_add, Finset.prod_add, Finset.prod_neg, mul_right_comm]

