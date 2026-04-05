import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_sum_eq_prod_toLeft_mul_prod_toRight (s : Finset (ι ⊕ κ)) (f : ι ⊕ κ → M) :
    ∏ x ∈ s, f x = (∏ x ∈ s.toLeft, f (Sum.inl x)) * ∏ x ∈ s.toRight, f (Sum.inr x) := by
  rw [← Finset.toLeft_disjSum_toRight (u := s), Finset.prod_disjSum, Finset.toLeft_disjSum,
    Finset.toRight_disjSum]

