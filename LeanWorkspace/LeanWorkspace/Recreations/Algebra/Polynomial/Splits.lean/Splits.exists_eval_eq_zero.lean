import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

theorem Splits.exists_eval_eq_zero (hf : Polynomial.Splits f) (hf0 : degree f ≠ 0) :
    ∃ a, eval a f = 0 := by
  obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset.mp hf
  by_cases hf₀ : f.leadingCoeff = 0
  · simp [leadingCoeff_eq_zero.mp hf₀]
  obtain rfl | ⟨a, ha⟩ := m.empty_or_exists_mem
  · rw [hm, Multiset.map_zero, Multiset.prod_zero, mul_one, degree_C hf₀] at hf0
    contradiction
  obtain ⟨m, rfl⟩ := Multiset.exists_cons_of_mem ha
  exact ⟨a, by rw [hm]; simp⟩

