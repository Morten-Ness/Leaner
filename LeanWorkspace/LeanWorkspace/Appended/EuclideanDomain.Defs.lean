import Mathlib

section

variable {R : Type u} [EuclideanDomain R]

theorem div_add_mod' (m k : R) : m / k * k + m % k = m := by
  rw [mul_comm]
  exact EuclideanDomain.div_add_mod _ _

end

section

variable {R : Type u} [EuclideanDomain R]

theorem div_add_mod (a b : R) : b * (a / b) + a % b = a := EuclideanDomain.quotient_mul_add_remainder_eq _ _

end

section

variable {R : Type u} [EuclideanDomain R]

variable [DecidableEq R]

theorem gcdA_zero_left {s : R} : EuclideanDomain.gcdA 0 s = 0 := by
  unfold EuclideanDomain.gcdA
  rw [EuclideanDomain.xgcd, EuclideanDomain.xgcd_zero_left]

end

section

variable {R : Type u} [EuclideanDomain R]

variable [DecidableEq R]

theorem gcdB_zero_left {s : R} : EuclideanDomain.gcdB 0 s = 1 := by
  unfold EuclideanDomain.gcdB
  rw [EuclideanDomain.xgcd, EuclideanDomain.xgcd_zero_left]

end

section

variable {R : Type u} [EuclideanDomain R]

theorem mod_add_div' (m k : R) : m % k + m / k * k = m := by
  rw [mul_comm]
  exact EuclideanDomain.mod_add_div _ _

end

section

variable {R : Type u} [EuclideanDomain R]

theorem mod_add_div (a b : R) : a % b + b * (a / b) = a := (add_comm _ _).trans (EuclideanDomain.div_add_mod _ _)

end

section

variable {R : Type u} [EuclideanDomain R]

theorem mod_zero (a : R) : a % 0 = a := by simpa only [zero_mul, zero_add] using EuclideanDomain.div_add_mod a 0

end

section

variable {R : Type u} [EuclideanDomain R]

variable [DecidableEq R]

theorem xgcdAux_rec {r s t r' s' t' : R} (h : r ≠ 0) :
    EuclideanDomain.xgcdAux r s t r' s' t' = EuclideanDomain.xgcdAux (r' % r) (s' - r' / r * s) (t' - r' / r * t) r s t := by
  conv =>
    lhs
    rw [EuclideanDomain.xgcdAux]
  exact if_neg h

end

section

variable {R : Type u} [EuclideanDomain R]

variable [DecidableEq R]

theorem xgcd_zero_left {s t r' s' t' : R} : EuclideanDomain.xgcdAux 0 s t r' s' t' = (r', s', t') := by
  unfold EuclideanDomain.xgcdAux
  exact if_pos rfl

end
