import Mathlib

variable {A B F : Type*} [FunLike F A B] (f : F)

variable [MonoidWithZero A] [GroupWithZero B] [MonoidWithZeroHomClass F A B] {f}

theorem restrict₀_eq_one_iff {a : A} : restrict₀ f a = 1 ↔ f a = 1 := by
  simp only [restrict₀_apply]
  split_ifs with H <;>
  simp [H, ← WithZero.coe_one, ← Units.mk0_one]

