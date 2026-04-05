import Mathlib

variable {G₀ G M α β : Type*}

variable [GroupWithZero α] [MulAction α β] {a : α}

theorem Commute.smul_left_iff₀ [Mul β] [SMulCommClass α β β] [IsScalarTower α β β] {x y : β}
    (ha : a ≠ 0) : Commute (a • x) y ↔ Commute x y := Commute.smul_left_iff (g := Units.mk0 a ha)

