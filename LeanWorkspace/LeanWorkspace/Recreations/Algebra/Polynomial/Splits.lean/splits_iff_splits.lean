import Mathlib

variable {R : Type*}

variable [Field R] {f g : R[X]}

theorem splits_iff_splits {f : R[X]} :
    Polynomial.Splits f ↔ f = 0 ∨ ∀ {g : R[X]}, Irreducible g → g ∣ f → degree g = 1 := by
  refine ⟨fun hf ↦ or_iff_not_imp_left.mpr fun h0 g hg hgf ↦
    (hf.of_dvd h0 hgf).degree_eq_one_of_irreducible hg, ?_⟩
  rintro (rfl | hf)
  · aesop
  classical
  by_cases hf0 : f = 0
  · simp [hf0]
  obtain ⟨u, hu⟩ := factors_prod hf0
  rw [← hu]
  refine (Polynomial.Splits.multisetProd fun g hg ↦ ?_).mul u.isUnit.splits
  exact Polynomial.Splits.of_degree_eq_one (hf (irreducible_of_factor g hg) (dvd_of_mem_factors hg))

