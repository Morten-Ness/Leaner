import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem mul_finsum_mem {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] {s : Set α}
    (f : α → R) (r : R) :
    (r * ∑ᶠ a ∈ s, f a) = ∑ᶠ a ∈ s, r * f a := by
  rw [mul_finsum]
  congr
  ext a
  by_cases h : a ∈ s <;> simp_all

