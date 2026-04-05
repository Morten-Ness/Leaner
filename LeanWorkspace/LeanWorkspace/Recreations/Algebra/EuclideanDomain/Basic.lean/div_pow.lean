import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

variable [DecidableEq R]

set_option backward.privateInPublic true in
private def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t

theorem div_pow {R : Type*} [EuclideanDomain R] {a b : R} {n : ℕ} (hab : b ∣ a) :
    (a / b) ^ n = a ^ n / b ^ n := by
  obtain ⟨c, rfl⟩ := hab
  obtain rfl | hb := eq_or_ne b 0
  · obtain rfl | hn := eq_or_ne n 0 <;> simp [*]
  · simp [hb, mul_pow]

