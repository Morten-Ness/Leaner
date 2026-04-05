import Mathlib

variable {R : Type*} {a b : R}

variable {ι R : Type*} [CommMonoid R] {s : Finset ι} {f : ι → R}

theorem IsLeftRegular.prod (h : ∀ i ∈ s, IsLeftRegular (f i)) :
    IsLeftRegular (∏ i ∈ s, f i) := s.prod_induction _ _ (@IsLeftRegular.mul R _) isRegular_one.left h

