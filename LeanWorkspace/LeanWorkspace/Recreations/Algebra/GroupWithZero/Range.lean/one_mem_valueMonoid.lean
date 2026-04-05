import Mathlib

variable {A B F : Type*} [FunLike F A B] (f : F)

variable [MonoidWithZero A] [MonoidWithZero B] [MonoidWithZeroHomClass F A B]

theorem one_mem_valueMonoid : 1 ∈ MonoidWithZeroHom.valueMonoid f := ⟨1, map_one ..⟩

