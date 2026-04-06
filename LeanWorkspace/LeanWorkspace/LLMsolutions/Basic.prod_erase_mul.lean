FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_erase_mul [DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι} (h : a ∈ s) :
    (∏ x ∈ s.erase a, f x) * f a = ∏ x ∈ s, f x := by
  classical
  exact (Finset.mul_prod_erase (s := s) (a := a) (f := f) h).symm
