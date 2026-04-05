import Mathlib

variable {A B F : Type*} [FunLike F A B] (f : F)

variable [MonoidWithZero A] [MonoidWithZero B] [MonoidWithZeroHomClass F A B]

theorem valueMonoid_eq_closure : MonoidWithZeroHom.valueMonoid f = Submonoid.closure ((↑) ⁻¹' (Set.range f)) := (MonoidWithZeroHom.valueMonoid f).closure_eq.symm

