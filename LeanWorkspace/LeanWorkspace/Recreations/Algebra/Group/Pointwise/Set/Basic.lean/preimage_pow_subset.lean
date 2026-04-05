import Mathlib

variable {F α β γ : Type*}

variable [Monoid α] [Monoid β] [FunLike F α β]

theorem preimage_pow_subset [MonoidHomClass F α β] (f : F) (s : Set β) :
    ∀ n, (f ⁻¹' s) ^ n ⊆ f ⁻¹' (s ^ n)
  | 0 => by simp [Set.subset_def]
  | n + 1 => by simpa [pow_succ] using Subset.trans (Set.mul_subset_mul_right
    (preimage_pow_subset f s n)) (Set.preimage_mul_preimage_subset f)
