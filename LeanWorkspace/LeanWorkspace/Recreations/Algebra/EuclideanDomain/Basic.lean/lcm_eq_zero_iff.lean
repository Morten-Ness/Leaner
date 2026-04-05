import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

variable [DecidableEq R]

set_option backward.privateInPublic true in
private def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t

theorem lcm_eq_zero_iff {x y : R} : lcm x y = 0 ↔ x = 0 ∨ y = 0 := by
  constructor
  · intro hxy
    rw [lcm, EuclideanDomain.mul_div_assoc _ (EuclideanDomain.gcd_dvd_right _ _), mul_eq_zero] at hxy
    apply Or.imp_right _ hxy
    intro hy
    by_cases hgxy : gcd x y = 0
    · rw [EuclideanDomain.gcd_eq_zero_iff] at hgxy
      exact hgxy.2
    · rcases EuclideanDomain.gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
      generalize gcd x y = g at hr hs hy hgxy ⊢
      subst hs
      rw [mul_div_cancel_left₀ _ hgxy] at hy
      rw [hy, mul_zero]
  rintro (hx | hy)
  · rw [hx, EuclideanDomain.lcm_zero_left]
  · rw [hy, EuclideanDomain.lcm_zero_right]

