import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommSemiring R]

theorem pow_sub_one_dvd_derivative_of_pow_dvd {p q : R[X]} {n : ℕ}
    (dvd : q ^ n ∣ p) : q ^ (n - 1) ∣ Polynomial.derivative p := by
  obtain ⟨r, rfl⟩ := dvd
  rw [Polynomial.derivative_mul, Polynomial.derivative_pow]
  exact (((dvd_mul_left _ _).mul_right _).mul_right _).add ((pow_dvd_pow q n.pred_le).mul_right _)

