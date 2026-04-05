import Mathlib

variable {R : Type*} {a b : R}

variable {ι R : Type*} [CommMonoid R] {s : Finset ι} {f : ι → R}

theorem IsRightRegular.prod (h : ∀ i ∈ s, IsRightRegular (f i)) :
    IsRightRegular (∏ i ∈ s, f i) := s.prod_induction _ _ (@IsRightRegular.mul R _) isRegular_one.right h

