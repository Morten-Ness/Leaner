import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoid M]

theorem prod_le_prod {p q : Multiset (Associates M)} (h : p ≤ q) : p.prod ≤ q.prod := by
  haveI := Classical.decEq (Associates M)
  suffices p.prod ≤ (p + (q - p)).prod by rwa [add_tsub_cancel_of_le h] at this
  suffices p.prod * 1 ≤ p.prod * (q - p).prod by simpa
  exact mul_mono (le_refl p.prod) one_le

