import Mathlib

section

variable {G₀ G M α β : Type*}

variable [GroupWithZero α] [MulAction α β] {a : α}

theorem Commute.smul_left_iff₀ [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {x y : β}
    (ha : a ≠ 0) : Commute (a • x) y ↔ Commute x y := Commute.smul_left_iff (g := Units.mk0 a ha)

end

section

variable {G₀ G M α β : Type*}

variable [GroupWithZero α] [MulAction α β] {a : α}

theorem Commute.smul_right_iff₀ [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {x y : β}
    (ha : a ≠ 0) : Commute x (a • y) ↔ Commute x y := Commute.smul_right_iff (g := Units.mk0 a ha)

end

section

variable {G₀ G M α β : Type*}

variable [GroupWithZero α] [MulAction α β] {a : α}

theorem eq_inv_smul_iff₀ (ha : a ≠ 0) {x y : β} : x = a⁻¹ • y ↔ a • x = y := eq_inv_smul_iff (g := Units.mk0 a ha)

end

section

variable {G₀ G M α β : Type*}

variable [GroupWithZero α] [MulAction α β] {a : α}

theorem inv_smul_eq_iff₀ (ha : a ≠ 0) {x y : β} : a⁻¹ • x = y ↔ x = a • y := inv_smul_eq_iff (g := Units.mk0 a ha)

end
