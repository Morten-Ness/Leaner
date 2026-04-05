import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem hasFiniteSupport_of_finsum_eq_one {R : Type*} [NonAssocSemiring R] {f : α → R}
    (h : ∑ᶠ i, f i = 1) : HasFiniteSupport f := by
  cases subsingleton_or_nontrivial R
  · simp_rw [HasFiniteSupport, Subsingleton.support_eq, finite_empty]
  · apply hasFiniteSupport_of_finsum_ne_zero
    rw [h]
    exact one_ne_zero

