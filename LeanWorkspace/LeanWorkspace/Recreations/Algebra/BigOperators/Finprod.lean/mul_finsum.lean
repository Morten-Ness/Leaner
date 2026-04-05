import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem mul_finsum {R : Type*} [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] (f : α → R)
    (r : R) :
    (r * ∑ᶠ a : α, f a) = ∑ᶠ a : α, r * f a := by
  by_cases hr : r = 0
  · simp_all
  by_cases h : f.support.Finite
  · exact mul_finsum' f r h
  simp [finsum_def, HasFiniteSupport, h, (by aesop : (r * f ·).support = f.support)]

