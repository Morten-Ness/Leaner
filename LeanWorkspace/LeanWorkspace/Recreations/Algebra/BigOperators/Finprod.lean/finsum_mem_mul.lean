import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finsum_mem_mul {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] {s : Set α}
    (f : α → R) (r : R) :
    (∑ᶠ a ∈ s, f a) * r = ∑ᶠ a ∈ s, f a * r := by
  rw [finsum_mul]
  congr
  ext a
  by_cases h : a ∈ s <;> simp_all

