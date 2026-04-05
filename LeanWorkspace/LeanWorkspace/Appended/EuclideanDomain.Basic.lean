import Mathlib

section

variable {R : Type u}

variable [EuclideanDomain R]

set_option backward.privateInPublic true in
private def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t

theorem add_mul_div_left (x y z : R) (h1 : y ≠ 0) (h2 : y ∣ x) : (x + y * z) / y = x / y + z := by
  rw [eq_comm]
  apply EuclideanDomain.eq_div_of_mul_eq_right h1
  rw [mul_add, EuclideanDomain.mul_div_cancel' h1 h2]

end

section

variable {R : Type u}

variable [EuclideanDomain R]

theorem div_dvd_of_dvd {p q : R} (hpq : q ∣ p) : p / q ∣ p := by
  by_cases hq : q = 0
  · rw [hq, zero_dvd_iff] at hpq
    rw [hpq]
    exact dvd_zero _
  use q
  rw [mul_comm, ← EuclideanDomain.mul_div_assoc _ hpq, mul_comm, mul_div_cancel_right₀ _ hq]

end

section

variable {R : Type u}

variable [EuclideanDomain R]

theorem eq_div_of_mul_eq_left {a b c : R} (hb : b ≠ 0) (h : a * b = c) : a = c / b := by
  rw [← h, mul_div_cancel_right₀ _ hb]

end

section

variable {R : Type u}

variable [EuclideanDomain R]

theorem eq_div_of_mul_eq_right {a b c : R} (ha : a ≠ 0) (h : a * b = c) : b = c / a := by
  rw [← h, mul_div_cancel_left₀ _ ha]

end

section

variable {R : Type u}

variable [EuclideanDomain R]

theorem mod_one (a : R) : a % 1 = 0 := EuclideanDomain.mod_eq_zero.2 (one_dvd _)

end

section

variable {R : Type u}

variable [EuclideanDomain R]

theorem mod_self (a : R) : a % a = 0 := EuclideanDomain.mod_eq_zero.2 dvd_rfl

end

section

variable {R : Type u}

variable [EuclideanDomain R]

theorem mul_div_cancel' {a b : R} (hb : b ≠ 0) (hab : b ∣ a) : b * (a / b) = a := by
  rw [← EuclideanDomain.mul_div_assoc _ hab, mul_div_cancel_left₀ _ hb]

-- This generalizes `Int.div_one`, see note [simp-normal form]

end

section

variable {R : Type u}

variable [EuclideanDomain R]

theorem zero_mod (b : R) : 0 % b = 0 := EuclideanDomain.mod_eq_zero.2 (dvd_zero _)

end
