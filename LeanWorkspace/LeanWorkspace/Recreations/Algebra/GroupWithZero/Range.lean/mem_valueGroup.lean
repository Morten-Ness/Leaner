import Mathlib

variable {A B F : Type*} [FunLike F A B] (f : F)

variable [MonoidWithZero A] [MonoidWithZero B] [MonoidWithZeroHomClass F A B]

theorem mem_valueGroup {b : Bˣ} (hb : b.1 ∈ Set.range f) : b ∈ MonoidWithZeroHom.valueGroup f := by
  suffices b ∈ MonoidWithZeroHom.valueMonoid f from Subgroup.mem_closure.mpr fun _ a ↦ a this
  exact MonoidWithZeroHom.mem_valueMonoid _ hb

