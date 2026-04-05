import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finsum_mul {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] (f : α → R)
    (r : R) :
    (∑ᶠ a : α, f a) * r = ∑ᶠ a : α, f a * r := by
  by_cases hr : r = 0
  · simp_all
  by_cases h : f.support.Finite
  · exact finsum_mul' f r h
  simp [finsum_def, HasFiniteSupport, h, (by aesop : (f · * r).support = f.support)]

