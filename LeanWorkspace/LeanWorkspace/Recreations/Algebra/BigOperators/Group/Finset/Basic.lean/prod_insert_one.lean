import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_insert_one [DecidableEq ι] (h : f a = 1) : ∏ x ∈ insert a s, f x = ∏ x ∈ s, f x := by
  simp [h]

