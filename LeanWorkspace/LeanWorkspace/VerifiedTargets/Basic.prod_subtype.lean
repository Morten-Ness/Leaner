import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_subtype {p : ι → Prop} {F : Fintype (Subtype p)} (s : Finset ι) (h : ∀ x, x ∈ s ↔ p x)
    (f : ι → M) : ∏ a ∈ s, f a = ∏ a : Subtype p, f a := by
  obtain rfl : p = (· ∈ s) := by simp [h]
  rw [← Finset.prod_coe_sort]
  congr!

