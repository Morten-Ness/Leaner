import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_mul_eq_prod_mul_of_exists {s : Finset ι} {f : ι → M} {b₁ b₂ : M}
    (a : ι) (ha : a ∈ s) (h : f a * b₁ = f a * b₂) :
    (∏ a ∈ s, f a) * b₁ = (∏ a ∈ s, f a) * b₂ := by
  classical
  rw [← insert_erase ha]
  simp only [mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true, Finset.prod_insert]
  rw [mul_assoc, mul_comm, mul_assoc, mul_comm b₁, h, ← mul_assoc, mul_comm _ (f a)]

