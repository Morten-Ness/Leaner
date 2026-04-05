import Mathlib

variable {A B F : Type*} [FunLike F A B] (f : F)

variable [MonoidWithZero A] [GroupWithZero B] [MonoidWithZeroHomClass F A B] {f}

theorem restrict₀_of_ne_zero {a : A} (h : f a ≠ 0) :
    restrict₀ f a = (⟨Units.mk0 (f a) h, MonoidWithZeroHom.mem_valueGroup _ ⟨a, rfl⟩⟩ : MonoidWithZeroHom.valueGroup f) := by
  simp [h, restrict₀_apply]

