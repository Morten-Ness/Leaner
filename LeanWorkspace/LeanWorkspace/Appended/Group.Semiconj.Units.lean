import Mathlib

section

open scoped Int

variable {M : Type*}

variable [Monoid M]

theorem mk_semiconjBy (u : Mˣ) (x : M) : SemiconjBy (↑u) x (u * x * ↑u⁻¹) := by
  unfold SemiconjBy; rw [Units.inv_mul_cancel_right]

end

section

open scoped Int

variable {M : Type*}

variable [Monoid M]

theorem units_inv_right {a : M} {x y : Mˣ} (h : SemiconjBy a x y) : SemiconjBy a ↑x⁻¹ ↑y⁻¹ := calc a * ↑x⁻¹
    _ = ↑y⁻¹ * (y * a) * ↑x⁻¹ := by rw [Units.inv_mul_cancel_left]
    _ = ↑y⁻¹ * a := by rw [← h.eq, mul_assoc, Units.mul_inv_cancel_right]

end

section

open scoped Int

variable {M : Type*}

variable [Monoid M]

theorem units_inv_right_iff {a : M} {x y : Mˣ} : SemiconjBy a ↑x⁻¹ ↑y⁻¹ ↔ SemiconjBy a x y := ⟨SemiconjBy.units_inv_right, SemiconjBy.units_inv_right⟩

end

section

open scoped Int

variable {M : Type*}

variable [Monoid M]

theorem units_inv_symm_left {a : Mˣ} {x y : M} (h : SemiconjBy (↑a) x y) : SemiconjBy (↑a⁻¹) y x := calc
    ↑a⁻¹ * y = ↑a⁻¹ * (y * a * ↑a⁻¹) := by rw [Units.mul_inv_cancel_right]
    _ = x * ↑a⁻¹ := by rw [← h.eq, ← mul_assoc, Units.inv_mul_cancel_left]

end

section

open scoped Int

variable {M : Type*}

variable [Monoid M]

theorem units_inv_symm_left_iff {a : Mˣ} {x y : M} : SemiconjBy (↑a⁻¹) y x ↔ SemiconjBy (↑a) x y := ⟨SemiconjBy.units_inv_symm_left, SemiconjBy.units_inv_symm_left⟩

end

section

open scoped Int

variable {M : Type*}

variable [Monoid M]

theorem units_val_iff {a x y : Mˣ} : SemiconjBy (a : M) x y ↔ SemiconjBy a x y := ⟨SemiconjBy.units_of_val, SemiconjBy.units_val⟩

end
