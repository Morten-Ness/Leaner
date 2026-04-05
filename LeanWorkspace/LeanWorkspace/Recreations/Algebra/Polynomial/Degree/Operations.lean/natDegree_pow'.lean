import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem natDegree_pow' {n : ℕ} (h : leadingCoeff p ^ n ≠ 0) : natDegree (p ^ n) = n * natDegree p := letI := Classical.decEq R
  if hp0 : p = 0 then
    if hn0 : n = 0 then by simp [*] else by rw [hp0, zero_pow hn0]; simp
  else
    have hpn : p ^ n ≠ 0 := fun hpn0 => by
      have h1 := h
      rw [← Polynomial.leadingCoeff_pow' h1, hpn0, leadingCoeff_zero] at h; exact h rfl
    Option.some_inj.1 <|
      show (natDegree (p ^ n) : WithBot ℕ) = (n * natDegree p : ℕ) by
        rw [← degree_eq_natDegree hpn, Polynomial.degree_pow' h, degree_eq_natDegree hp0]; simp

