import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

variable [DecidableEq R]

set_option backward.privateInPublic true in
private def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t

theorem dvd_lcm_left (x y : R) : x ∣ lcm x y := by _cases
    (fun hxy : gcd x y = 0 => by
      rw [lcm, hxy, div_zero]
      exact dvd_zero _)
    fun hxy =>
    let ⟨z, hz⟩ := (EuclideanDomain.gcd_dvd x y).2
    ⟨z, Eq.symm <| EuclideanDomain.eq_div_of_mul_eq_left hxy <| by rw [mul_right_comm, mul_assoc, ← hz]⟩

