import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem isMonicOfDegree_iff_of_subsingleton [Subsingleton R] {p : R[X]} {n : ℕ} :
    IsMonicOfDegree p n ↔ n = 0 := by
  rw [Subsingleton.eq_one p]
  refine ⟨fun ⟨H, _⟩ ↦ ?_, fun H ↦ ?_⟩
  · rwa [natDegree_one, eq_comm] at H
  · rw [H, Polynomial.isMonicOfDegree_zero_iff]

