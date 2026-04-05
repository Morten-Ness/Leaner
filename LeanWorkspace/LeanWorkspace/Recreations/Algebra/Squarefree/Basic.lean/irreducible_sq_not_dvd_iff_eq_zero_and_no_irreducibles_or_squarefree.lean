import Mathlib

variable {R : Type*}

variable [CommMonoidWithZero R] [WfDvdMonoid R]

theorem irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree (r : R) :
    (∀ x : R, Irreducible x → ¬x * x ∣ r) ↔ (r = 0 ∧ ∀ x : R, ¬Irreducible x) ∨ Squarefree r := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases eq_or_ne r 0 with (rfl | hr)
    · exact .inl (by simpa using h)
    · exact .inr ((squarefree_iff_no_irreducibles hr).mpr h)
  · rintro (⟨rfl, h⟩ | h)
    · simpa using h
    intro x hx t
    exact hx.not_isUnit (h x t)

