FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_set_coe (s : Set ι) [Fintype s] : (∏ i : s, f i) = ∏ i ∈ s.toFinset, f i := by
  classical
  exact Fintype.prod_subtype (s := s) (f := f)
