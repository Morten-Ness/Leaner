import Mathlib

variable {A B F : Type*} [FunLike F A B] (f : F)

variable [MonoidWithZero A] [MonoidWithZero B] [MonoidWithZeroHomClass F A B]

theorem mem_valueMonoid {b : Bˣ} (hb : b.val ∈ Set.range f) : b ∈ MonoidWithZeroHom.valueMonoid f := by
  tauto

