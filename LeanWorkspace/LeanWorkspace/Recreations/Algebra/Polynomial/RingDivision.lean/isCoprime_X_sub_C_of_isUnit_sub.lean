import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R]

variable [IsDomain R] {p q : R[X]}

theorem isCoprime_X_sub_C_of_isUnit_sub {R} [CommRing R] {a b : R} (h : IsUnit (a - b)) :
    IsCoprime (Polynomial.X - Polynomial.C a) (Polynomial.X - Polynomial.C b) := ⟨-Polynomial.C h.unit⁻¹.val, Polynomial.C h.unit⁻¹.val, by
    rw [neg_mul_comm, ← left_distrib, neg_add_eq_sub, sub_sub_sub_cancel_left, ← C_sub, ← C_mul]
    rw [← C_1]
    congr
    exact h.val_inv_mul⟩

