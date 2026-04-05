import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem lt_natDegree_of_mem_eraseLead_support {a : ℕ} (h : a ∈ (Polynomial.eraseLead f).support) :
    a < f.natDegree := by
  rw [Polynomial.eraseLead_support, mem_erase] at h
  exact (le_natDegree_of_mem_supp a h.2).lt_of_ne h.1

