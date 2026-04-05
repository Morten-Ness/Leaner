import Mathlib

section

variable {A B F : Type*} [FunLike F A B] (f : F)

variable [MonoidWithZero A] [MonoidWithZero B] [MonoidWithZeroHomClass F A B]

theorem inv_mem_valueGroup {b : Bˣ} (hb : b.1 ∈ Set.range f) : b⁻¹ ∈ MonoidWithZeroHom.valueGroup f := Subgroup.inv_mem _ (MonoidWithZeroHom.mem_valueGroup f hb)

end

section

variable {A B F : Type*} [FunLike F A B] (f : F)

variable [MonoidWithZero A] [MonoidWithZero B] [MonoidWithZeroHomClass F A B]

theorem mem_valueGroup {b : Bˣ} (hb : b.1 ∈ Set.range f) : b ∈ MonoidWithZeroHom.valueGroup f := by
  suffices b ∈ MonoidWithZeroHom.valueMonoid f from Subgroup.mem_closure.mpr fun _ a ↦ a this
  exact MonoidWithZeroHom.mem_valueMonoid _ hb

end

section

variable {A B F : Type*} [FunLike F A B] (f : F)

variable [MonoidWithZero A] [MonoidWithZero B] [MonoidWithZeroHomClass F A B]

theorem valueMonoid_eq_closure : MonoidWithZeroHom.valueMonoid f = Submonoid.closure ((↑) ⁻¹' (Set.range f)) := (MonoidWithZeroHom.valueMonoid f).closure_eq.symm

end
