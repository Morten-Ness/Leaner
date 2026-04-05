import Mathlib

open scoped Cardinal Pointwise

variable {G₀ M₀ : Type*}

variable [GroupWithZero G₀] [Zero M₀] [MulActionWithZero G₀ M₀] {a : G₀}

theorem natCard_smul_set₀ (ha : a ≠ 0) (s : Set M₀) : Nat.card ↥(a • s) = Nat.card s := Nat.card_image_of_injective (MulAction.injective₀ ha) _

