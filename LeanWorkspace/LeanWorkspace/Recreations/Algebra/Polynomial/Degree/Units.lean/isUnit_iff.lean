import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

theorem isUnit_iff : IsUnit p ↔ ∃ r : R, IsUnit r ∧ Polynomial.C r = p := ⟨fun hp =>
    ⟨p.coeff 0,
      let h := eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_isUnit hp)
      ⟨isUnit_C.1 (h ▸ hp), h.symm⟩⟩,
    fun ⟨_, hr, hrp⟩ => hrp ▸ isUnit_C.2 hr⟩

