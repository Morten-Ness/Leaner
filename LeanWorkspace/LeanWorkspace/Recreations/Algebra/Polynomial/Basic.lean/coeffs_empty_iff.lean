import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeffs_empty_iff {p : R[X]} : Polynomial.coeffs p = ∅ ↔ p = 0 := by
  refine ⟨?_, fun h ↦ by simp [h]⟩
  contrapose!
  intro h
  rw [← support_nonempty] at h
  obtain ⟨n, hn⟩ := h
  rw [Polynomial.mem_support_iff] at hn
  exact ⟨p.coeff n, Polynomial.coeff_mem_coeffs hn⟩

