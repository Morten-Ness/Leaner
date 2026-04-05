import Mathlib

variable {ι α M N : Type*}

variable [Monoid M]

variable [Preorder M] [CanonicallyOrderedMul M]

theorem le_prod_of_mem {xs : List M} {x : M} (h₁ : x ∈ xs) : x ≤ xs.prod := by
  induction xs with
  | nil => simp at h₁
  | cons y ys ih =>
    simp only [mem_cons] at h₁
    rcases h₁ with (rfl | h₁)
    · simp
    · specialize ih h₁
      simp only [List.prod_cons]
      exact le_mul_left ih

