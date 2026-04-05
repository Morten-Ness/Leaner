import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem X_pow_dvd_iff {f : R[X]} {n : ℕ} : Polynomial.X ^ n ∣ f ↔ ∀ d < n, f.coeff d = 0 := ⟨fun ⟨g, hgf⟩ d hd => by
    simp only [hgf, coeff_X_pow_mul', ite_eq_right_iff, not_le_of_gt hd, IsEmpty.forall_iff],
    fun hd => by
    induction n with
    | zero => simp [pow_zero]
    | succ n hn =>
      obtain ⟨g, hgf⟩ := hn fun d : ℕ => fun H : d < n => hd _ (Nat.lt_succ_of_lt H)
      have := coeff_X_pow_mul g n 0
      rw [zero_add, ← hgf, hd n (Nat.lt_succ_self n)] at this
      obtain ⟨k, hgk⟩ := Polynomial.X_dvd_iff.mpr this.symm
      use k
      rwa [pow_succ, mul_assoc, ← hgk]⟩

