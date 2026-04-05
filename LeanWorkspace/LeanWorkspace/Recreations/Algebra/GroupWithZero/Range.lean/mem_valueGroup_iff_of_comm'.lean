import Mathlib

variable [GroupWithZero A] [GroupWithZero B] [MonoidWithZeroHomClass F A B] {f}

variable [MonoidWithZero A] [CommGroupWithZero B] [MonoidWithZeroHomClass F A B]

theorem mem_valueGroup_iff_of_comm' {y : Bˣ} :
    y ∈ MonoidWithZeroHom.valueGroup f ↔ ∃ a, f a ≠ 0 ∧ ∃ x, f x ≠ 0 ∧ f a * y = f x := by
  rw [mem_valueGroup_iff_of_comm]
  exact ⟨fun ⟨a, ha, x, hax⟩ ↦ ⟨a, ha, x, by aesop, hax⟩, fun ⟨a, ha, x, hx, hax⟩ ↦ ⟨a, ha, x, hax⟩⟩

