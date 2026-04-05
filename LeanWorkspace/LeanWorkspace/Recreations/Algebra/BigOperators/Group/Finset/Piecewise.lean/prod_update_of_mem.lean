import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_update_of_mem [DecidableEq ι] {s : Finset ι} {i : ι} (h : i ∈ s) (f : ι → M) (b : M) :
    ∏ x ∈ s, Function.update f i b x = b * ∏ x ∈ s \ singleton i, f x := by
  rw [update_eq_piecewise, Finset.prod_piecewise]
  simp [h]

