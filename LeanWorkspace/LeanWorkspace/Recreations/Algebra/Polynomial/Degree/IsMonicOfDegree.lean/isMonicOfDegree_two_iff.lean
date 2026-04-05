import Mathlib

variable {R : Type*}

variable [Semiring R]

variable [Nontrivial R]

theorem isMonicOfDegree_two_iff {f : R[X]} :
    IsMonicOfDegree f 2 ↔ ∃ a b : R, f = X ^ 2 + C a * X + C b := by
  refine ⟨fun H ↦ ?_, fun ⟨a, b, h⟩ ↦ h ▸ Polynomial.isMonicOfDegree_add_add_two a b⟩
  refine ⟨f.coeff 1, f.coeff 0, ext fun n ↦ ?_⟩
  rcases lt_trichotomy n 1 with hn | rfl | hn
  · obtain rfl : n = 0 := Nat.lt_one_iff.mp hn
    simp
  · simp
  · exact H.coeff_eq (Polynomial.isMonicOfDegree_add_add_two ..) (by lia)

