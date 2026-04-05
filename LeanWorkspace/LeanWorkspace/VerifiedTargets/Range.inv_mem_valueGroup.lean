import Mathlib

variable {A B F : Type*} [FunLike F A B] (f : F)

variable [MonoidWithZero A] [MonoidWithZero B] [MonoidWithZeroHomClass F A B]

theorem inv_mem_valueGroup {b : Bˣ} (hb : b.1 ∈ Set.range f) : b⁻¹ ∈ MonoidWithZeroHom.valueGroup f := Subgroup.inv_mem _ (MonoidWithZeroHom.mem_valueGroup f hb)

