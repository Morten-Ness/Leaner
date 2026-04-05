import Mathlib

open scoped Polynomial

variable (p q : ℤ[X])

theorem irreducible_aux3 {k m m' n : ℕ} (hkm : k < m) (hmn : m < n) (hkm' : k < m') (hmn' : m' < n)
    (u v w x z : Units ℤ) (hp : p = Polynomial.trinomial k m n (u : ℤ) v w)
    (hq : q = Polynomial.trinomial k m' n (x : ℤ) v z) (h : p * p.mirror = q * q.mirror) :
    q = p ∨ q = p.mirror := by
  have hmul := congr_arg leadingCoeff h
  rw [leadingCoeff_mul, leadingCoeff_mul, mirror_leadingCoeff, mirror_leadingCoeff, hp, hq,
    Polynomial.trinomial_leadingCoeff hkm hmn Polynomial.IsUnitTrinomial.ne_zero w, Polynomial.trinomial_leadingCoeff hkm' hmn' Polynomial.IsUnitTrinomial.ne_zero z,
    Polynomial.trinomial_trailingCoeff hkm hmn Polynomial.IsUnitTrinomial.ne_zero u, Polynomial.trinomial_trailingCoeff hkm' hmn' Polynomial.IsUnitTrinomial.ne_zero x]
    at hmul
  have hadd := congr_arg (eval 1) h
  rw [eval_mul, eval_mul, mirror_eval_one, mirror_eval_one, ← sq, ← sq, hp, hq] at hadd
  simp only [eval_add, eval_C_mul, eval_X_pow, one_pow, mul_one, Polynomial.trinomial_def] at hadd
  rw [add_assoc, add_assoc, add_comm (u : ℤ), add_comm (x : ℤ), add_assoc, add_assoc] at hadd
  simp only [add_sq', add_assoc, add_right_inj, ← Units.val_pow_eq_pow_val, Int.units_sq] at hadd
  rw [mul_assoc, hmul, ← mul_assoc, add_right_inj,
    mul_right_inj' (show 2 * (v : ℤ) ≠ 0 from mul_ne_zero two_ne_zero Polynomial.IsUnitTrinomial.ne_zero v)] at hadd
  replace hadd :=
    (Int.isUnit_add_isUnit_eq_isUnit_add_isUnit w.isUnit u.isUnit z.isUnit x.isUnit).mp hadd
  simp only [Units.val_inj] at hadd
  rcases hadd with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact Polynomial.IsUnitTrinomial.irreducible_aux2 hkm hmn hkm' hmn' u v w hp hq h
  · rw [← mirror_inj, Polynomial.trinomial_mirror hkm' hmn' Polynomial.IsUnitTrinomial.ne_zero w Polynomial.IsUnitTrinomial.ne_zero u] at hq
    rw [mul_comm q, ← q.mirror_mirror, q.mirror.mirror_mirror] at h
    rw [← mirror_inj, or_comm, ← mirror_eq_iff]
    exact
      Polynomial.IsUnitTrinomial.irreducible_aux2 hkm hmn (lt_add_of_pos_left k (tsub_pos_of_lt hmn'))
        (lt_tsub_iff_right.mp ((tsub_lt_tsub_iff_left_of_le hmn'.le).mpr hkm')) u v w hp hq h

