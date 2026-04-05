import Mathlib

variable {A B F : Type*} [FunLike F A B] (f : F)

variable [MonoidWithZero A] [MonoidWithZero B] [MonoidWithZeroHomClass F A B]

theorem mem_valueMonoid_iff {b : Bˣ} : b ∈ MonoidWithZeroHom.valueMonoid f ↔ b ∈ (↑) ⁻¹' (Set.range f) := Iff.rfl

