import Mathlib

open scoped Polynomial

variable {R : Type u} [Semiring R] {S : Type v} [Semiring S] {f : R →+* S}

theorem exists_degree_eq_of_mem_lifts {p : S[X]} (hlifts : p ∈ Polynomial.lifts f) :
    ∃ q : R[X], map f q = p ∧ q.degree = p.degree := by
  obtain ⟨q, hq, hq'⟩ := Polynomial.exists_support_eq_of_mem_lifts hlifts
  exact ⟨q, hq, congrArg Finset.max hq'⟩

