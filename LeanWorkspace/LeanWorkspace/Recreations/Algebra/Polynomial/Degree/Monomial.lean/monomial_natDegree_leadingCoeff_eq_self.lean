import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem monomial_natDegree_leadingCoeff_eq_self (h : #p.support ≤ 1) :
    monomial p.natDegree p.leadingCoeff = p := by
  classical
  rcases card_support_le_one_iff_monomial.1 h with ⟨n, a, rfl⟩
  by_cases ha : a = 0 <;> simp [ha]

