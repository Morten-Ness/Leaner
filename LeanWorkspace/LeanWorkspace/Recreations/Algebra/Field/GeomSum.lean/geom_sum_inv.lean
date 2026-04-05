import Mathlib

variable {R K : Type*}

variable [DivisionRing K] {x y : K}

theorem geom_sum_inv (hx1 : x ≠ 1) (hx0 : x ≠ 0) (n : ℕ) :
    ∑ i ∈ range n, x⁻¹ ^ i = (x - 1)⁻¹ * (x - x⁻¹ ^ n * x) := by
  have h₁ : x⁻¹ ≠ 1 := by rwa [inv_eq_one_div, Ne, div_eq_iff_mul_eq hx0, one_mul]
  have h₂ : x⁻¹ - 1 ≠ 0 := mt sub_eq_zero.1 h₁
  have h₃ : x - 1 ≠ 0 := mt sub_eq_zero.1 hx1
  have h₄ : x * (x ^ n)⁻¹ = (x ^ n)⁻¹ * x :=
    Nat.recOn n (by simp) fun n h => by
      rw [pow_succ', mul_inv_rev, ← mul_assoc, h, mul_assoc, mul_inv_cancel₀ hx0, mul_assoc,
        inv_mul_cancel₀ hx0]
  rw [geom_sum_eq h₁, div_eq_iff_mul_eq h₂, ← mul_right_inj' h₃, ← mul_assoc, ← mul_assoc,
    mul_inv_cancel₀ h₃]
  simp only [inv_pow, sub_eq_add_neg, mul_add, one_mul, mul_neg, add_mul, mul_inv_cancel₀ hx0,
    neg_mul, mul_assoc, mul_one, add_comm, neg_add_rev, neg_neg, h₄, add_left_comm]
  rw [add_comm _ (-x), add_assoc, add_assoc _ _ 1]

