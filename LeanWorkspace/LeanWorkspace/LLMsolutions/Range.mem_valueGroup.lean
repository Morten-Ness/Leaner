FAIL
import Mathlib

variable {A B F : Type*} [FunLike F A B] (f : F)

variable [MonoidWithZero A] [MonoidWithZero B] [MonoidWithZeroHomClass F A B]

theorem mem_valueGroup {b : Bˣ} (hb : b.1 ∈ Set.range f) : b ∈ MonoidWithZeroHom.valueGroup f := by
  rw [MonoidWithZeroHom.mem_valueGroup_iff] at ⊢
  exact hb
