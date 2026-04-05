import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

variable [DecidableEq R]

set_option backward.privateInPublic true in
private def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t

theorem lcm_dvd {x y z : R} (hxz : x ∣ z) (hyz : y ∣ z) : lcm x y ∣ z := by
  rw [lcm]
  by_cases hxy : gcd x y = 0
  · rw [hxy, div_zero]
    rw [EuclideanDomain.gcd_eq_zero_iff] at hxy
    rwa [hxy.1] at hxz
  rcases EuclideanDomain.gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
  suffices x * y ∣ z * gcd x y by
    obtain ⟨p, hp⟩ := this
    use p
    generalize gcd x y = g at hxy hs hp ⊢
    subst hs
    rw [mul_left_comm, mul_div_cancel_left₀ _ hxy, ← mul_left_inj' hxy, hp]
    rw [← mul_assoc]
    simp only [mul_right_comm]
  rw [EuclideanDomain.gcd_eq_gcd_ab, mul_add]
  apply dvd_add
  · rw [mul_left_comm]
    gcongr
    apply hyz.mul_right
  · rw [mul_left_comm, mul_comm]
    gcongr
    apply hxz.mul_right

