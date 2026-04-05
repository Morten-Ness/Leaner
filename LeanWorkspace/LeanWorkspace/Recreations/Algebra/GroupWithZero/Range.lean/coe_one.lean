import Mathlib

variable {A B F : Type*} [FunLike F A B] (f : F)

variable [MonoidWithZero A] [MonoidWithZero B] [MonoidWithZeroHomClass F A B]

theorem coe_one : (⟨(1 : Bˣ), MonoidWithZeroHom.one_mem_valueMonoid f⟩ : MonoidWithZeroHom.valueMonoid f) = 1 := rfl

