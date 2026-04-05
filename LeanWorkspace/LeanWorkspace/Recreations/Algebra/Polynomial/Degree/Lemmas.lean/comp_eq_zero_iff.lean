import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

theorem comp_eq_zero_iff [Semiring R] [NoZeroDivisors R] {p q : R[X]} :
    p.comp q = 0 ↔ p = 0 ∨ p.eval (q.coeff 0) = 0 ∧ q = Polynomial.C (q.coeff 0) := by
  refine ⟨fun h ↦ ?_, Or.rec (fun h ↦ by simp [h]) fun h ↦ by rw [h.2, comp_C, h.1, C_0]⟩
  have key : p.natDegree = 0 ∨ q.natDegree = 0 := by
    rw [← mul_eq_zero, ← Polynomial.natDegree_comp, h, natDegree_zero]
  obtain key | key := Or.imp eq_C_of_natDegree_eq_zero eq_C_of_natDegree_eq_zero key
  · rw [key, C_comp] at h
    exact Or.inl (key.trans h)
  · rw [key, comp_C, C_eq_zero] at h
    exact Or.inr ⟨h, key⟩

