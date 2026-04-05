import Mathlib

section

variable {G₀ : Type u} {M₀ : Type*}

variable [CommMagma M₀] [Zero M₀]

theorem IsLeftCancelMulZero.to_isCancelMulZero [IsLeftCancelMulZero M₀] :
    IsCancelMulZero M₀ := { IsLeftCancelMulZero.to_isRightCancelMulZero with }

end

section

variable {G₀ : Type u} {M₀ : Type*}

variable [CommMagma M₀] [Zero M₀]

theorem IsLeftCancelMulZero.to_isRightCancelMulZero [IsLeftCancelMulZero M₀] :
    IsRightCancelMulZero M₀ where
  mul_right_cancel_of_ne_zero := fun hb _ _ h => mul_left_cancel₀ hb <| (mul_comm _ _).trans (h.trans (mul_comm _ _))

end

section

variable {G₀ : Type u} {M₀ : Type*}

variable [CommMagma M₀] [Zero M₀]

theorem IsRightCancelMulZero.to_isCancelMulZero [IsRightCancelMulZero M₀] :
    IsCancelMulZero M₀ := { IsRightCancelMulZero.to_isLeftCancelMulZero with }

end

section

variable {G₀ : Type u} {M₀ : Type*}

variable [CommMagma M₀] [Zero M₀]

theorem IsRightCancelMulZero.to_isLeftCancelMulZero [IsRightCancelMulZero M₀] :
    IsLeftCancelMulZero M₀ where
  mul_left_cancel_of_ne_zero := fun hb _ _ h => mul_right_cancel₀ hb <| (mul_comm _ _).trans (h.trans (mul_comm _ _))

end

section

variable {G₀ : Type u} {M₀ : Type*}

theorem eq_zero_or_one_of_sq_eq_self [MonoidWithZero M₀] [IsRightCancelMulZero M₀]
    {x : M₀} (hx : x ^ 2 = x) :
    x = 0 ∨ x = 1 := or_iff_not_imp_left.mpr (mul_left_injective₀ · <| by simpa [sq] using hx)

end

section

variable {G₀ : Type u} {M₀ : Type*}

theorem isCancelMulZero_iff_forall_isRegular {M₀} [Mul M₀] [Zero M₀] :
    IsCancelMulZero M₀ ↔ ∀ {a : M₀}, a ≠ 0 → IsRegular a := by
  simp only [isCancelMulZero_iff, isLeftCancelMulZero_iff, isRightCancelMulZero_iff, ← forall_and]
  exact forall₂_congr fun _ _ ↦ isRegular_iff.symm

end

section

variable {G₀ : Type u} {M₀ : Type*}

variable [MulZeroClass M₀]

variable [NoZeroDivisors M₀] {a b : M₀}

theorem mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0 := ⟨eq_zero_or_eq_zero_of_mul_eq_zero,
    fun o ↦ o.elim (fun h ↦ mul_eq_zero_of_left h b) (mul_eq_zero_of_right a)⟩

end

section

variable {G₀ : Type u} {M₀ : Type*}

variable [MulZeroClass M₀]

variable [NoZeroDivisors M₀] {a b : M₀}

theorem mul_eq_zero_comm : a * b = 0 ↔ b * a = 0 := mul_eq_zero.trans <| or_comm.trans mul_eq_zero.symm

end

section

variable {G₀ : Type u} {M₀ : Type*}

variable [GroupWithZero G₀] {a b : G₀}

theorem mul_inv_cancel_left₀ (h : a ≠ 0) (b : G₀) : a * (a⁻¹ * b) = b := calc
    a * (a⁻¹ * b) = a * a⁻¹ * b := (mul_assoc _ _ _).symm
    _ = b := by simp [h]

end

section

variable {G₀ : Type u} {M₀ : Type*}

variable [GroupWithZero G₀] {a b : G₀}

theorem mul_inv_cancel_right₀ (h : b ≠ 0) (a : G₀) : a * b * b⁻¹ = a := calc
    a * b * b⁻¹ = a * (b * b⁻¹) := mul_assoc _ _ _
    _ = a := by simp [h]

end

section

variable {G₀ : Type u} {M₀ : Type*}

variable [GroupWithZero G₀] {a : G₀}

theorem mul_inv_cancel₀ (h : a ≠ 0) : a * a⁻¹ = 1 := GroupWithZero.mul_inv_cancel a h

-- See note [lower instance priority]

end

section

variable {G₀ : Type u} {M₀ : Type*}

variable [Mul M₀] [Zero M₀] [IsLeftCancelMulZero M₀] {a b c : M₀}

theorem mul_left_cancel₀ (ha : a ≠ 0) (h : a * b = a * c) : b = c := IsLeftCancelMulZero.mul_left_cancel_of_ne_zero ha h

end

section

variable {G₀ : Type u} {M₀ : Type*}

variable [Mul M₀] [Zero M₀] [IsRightCancelMulZero M₀] {a b c : M₀}

theorem mul_right_cancel₀ (hb : b ≠ 0) (h : a * b = c * b) : a = c := IsRightCancelMulZero.mul_right_cancel_of_ne_zero hb h

end

section

variable {G₀ : Type u} {M₀ : Type*}

variable [MulZeroClass M₀]

theorem noZeroDivisors_iff_eq_zero_of_mul :
    NoZeroDivisors M₀ ↔ ∀ x : M₀, x ≠ 0 → (∀ y, x * y = 0 → y = 0) ∧ (∀ y, y * x = 0 → y = 0) := by
  simp only [forall_and, ← noZeroDivisors_iff_right_eq_zero_of_mul,
    ← noZeroDivisors_iff_left_eq_zero_of_mul, and_self]

end

section

variable {G₀ : Type u} {M₀ : Type*}

variable [MulZeroClass M₀]

theorem noZeroDivisors_iff_left_eq_zero_of_mul :
    NoZeroDivisors M₀ ↔ ∀ x : M₀, x ≠ 0 → ∀ y, y * x = 0 → y = 0 := by
  simp only [noZeroDivisors_iff, or_iff_not_imp_right]
  exact ⟨fun h b hb a eq ↦ h eq hb, fun h a b eq hb ↦ h b hb a eq⟩

end

section

variable {G₀ : Type u} {M₀ : Type*}

variable [MulZeroClass M₀]

theorem noZeroDivisors_iff_right_eq_zero_of_mul :
    NoZeroDivisors M₀ ↔ ∀ x : M₀, x ≠ 0 → ∀ y, x * y = 0 → y = 0 := by
  simp only [noZeroDivisors_iff, or_iff_not_imp_left]
  exact ⟨fun h a ha b eq ↦ h eq ha, fun h a b eq ha ↦ h a ha b eq⟩

end

section

variable {G₀ : Type u} {M₀ : Type*}

variable [MonoidWithZero M₀]

theorem pow_mul_apply_eq_pow_mul {M : Type*} [Monoid M] (f : M₀ → M) {x : M₀}
    (hx : ∀ y : M₀, f (x * y) = f x * f y) (n : ℕ) :
    ∀ (y : M₀), f (x ^ n * y) = f x ^ n * f y := by
  induction n with
  | zero => intro y; rw [pow_zero, pow_zero, one_mul, one_mul]
  | succ n hn => intro y; rw [pow_succ', pow_succ', mul_assoc, mul_assoc, hx, hn]

end
