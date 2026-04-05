import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

variable [DecidableEq R]

set_option backward.privateInPublic true in
private def P (a b : R) : R × R × R → Prop
  | (r, s, t) => (r : R) = a * s + b * t

theorem gcd_eq_gcd_ab (a b : R) : (gcd a b : R) = a * gcdA a b + b * gcdB a b := by
  have :=
    @EuclideanDomain.xgcdAux_P _ _ _ a b a b 1 0 0 1 (by dsimp [P]; rw [mul_one, mul_zero, add_zero])
      (by dsimp [P]; rw [mul_one, mul_zero, zero_add])
  rwa [EuclideanDomain.xgcdAux_val, xgcd_val] at this

-- see Note [lower instance priority]

