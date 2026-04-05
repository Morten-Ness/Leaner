import Mathlib

variable {A B F : Type*} [FunLike F A B] (f : F)

variable [MonoidWithZero A] [GroupWithZero B] [MonoidWithZeroHomClass F A B] {f}

theorem restrict₀_eq_zero_iff {a : A} : restrict₀ f a = 0 ↔ f a = 0 := by simp [restrict₀_apply]

