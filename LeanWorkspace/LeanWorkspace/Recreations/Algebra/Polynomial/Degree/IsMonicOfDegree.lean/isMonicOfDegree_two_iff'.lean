import Mathlib

variable {R : Type*}

variable [Ring R]

variable [Nontrivial R]

theorem isMonicOfDegree_two_iff' {f : R[X]} :
    IsMonicOfDegree f 2 ↔ ∃ a b : R, f = X ^ 2 - C a * X + C b := by
  refine ⟨fun H ↦ ?_, fun ⟨a, b, h⟩ ↦ h ▸ Polynomial.isMonicOfDegree_sub_add_two a b⟩
  simp only [sub_eq_add_neg, ← neg_mul, ← map_neg]
  obtain ⟨a, b, h⟩ := Polynomial.isMonicOfDegree_two_iff.mp H
  exact ⟨-a, b, (neg_neg a).symm ▸ h⟩

