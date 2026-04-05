import Mathlib

open scoped Polynomial

variable {R : Type u} [Semiring R] {S : Type v} [Semiring S] {f : R →+* S}

theorem lifts_and_natDegree_eq_and_monic {p : S[X]} (hlifts : p ∈ Polynomial.lifts f) (hp : p.Monic) :
    ∃ q : R[X], map f q = p ∧ q.natDegree = p.natDegree ∧ q.Monic := by
  rcases subsingleton_or_nontrivial S with hR | hR
  · obtain rfl : p = 1 := Subsingleton.elim _ _
    exact ⟨1, Subsingleton.elim _ _, by simp, by simp⟩
  obtain ⟨p', h₁, h₂, h₃⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hp
  exact ⟨p', h₁, natDegree_eq_of_degree_eq h₂, h₃⟩

