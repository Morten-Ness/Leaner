import Mathlib

variable {A B F : Type*} [FunLike F A B] (f : F)

variable [MonoidWithZero A] [MonoidWithZero B] [MonoidWithZeroHomClass F A B]

theorem valueGroup_def : MonoidWithZeroHom.valueGroup f = Subgroup.closure (MonoidWithZeroHom.valueMonoid f) := rfl

