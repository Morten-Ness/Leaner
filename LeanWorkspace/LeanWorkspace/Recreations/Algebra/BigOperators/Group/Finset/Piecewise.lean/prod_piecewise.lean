import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_piecewise [DecidableEq ι] (s t : Finset ι) (f g : ι → M) :
    (∏ x ∈ s, (t.piecewise f g) x) = (∏ x ∈ s ∩ t, f x) * ∏ x ∈ s \ t, g x := by
  simp only [piecewise]
  rw [Finset.prod_ite, filter_mem_eq_inter, ← sdiff_eq_filter]

