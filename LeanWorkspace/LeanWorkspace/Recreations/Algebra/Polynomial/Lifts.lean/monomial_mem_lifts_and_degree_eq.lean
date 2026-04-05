import Mathlib

open scoped Polynomial

variable {R : Type u} [Semiring R] {S : Type v} [Semiring S] {f : R →+* S}

theorem monomial_mem_lifts_and_degree_eq {s : S} {n : ℕ} (hl : monomial n s ∈ Polynomial.lifts f) :
    ∃ q : R[X], map f q = monomial n s ∧ q.degree = (monomial n s).degree := by
  rcases eq_or_ne s 0 with rfl | h
  · exact ⟨0, by simp⟩
  obtain ⟨a, rfl⟩ := coeff_monomial_same n s ▸ Polynomial.lifts_iff_coeff_lifts (monomial n s).mp hl n
  refine ⟨monomial n a, map_monomial f, ?_⟩
  rw [degree_monomial, degree_monomial n h]
  exact mt (fun ha ↦ ha ▸ map_zero f) h

