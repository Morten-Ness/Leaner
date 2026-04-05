import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_cancels_of_partition_cancels (R : Setoid ι) [DecidableRel R]
    (h : ∀ x ∈ s, ∏ a ∈ s with R a x, f a = 1) : ∏ x ∈ s, f x = 1 := by
  rw [Finset.prod_partition R, ← Finset.prod_eq_one]
  intro xbar xbar_in_s
  obtain ⟨x, x_in_s, rfl⟩ := mem_image.mp xbar_in_s
  simp only [← Quotient.eq] at h
  exact h x x_in_s

