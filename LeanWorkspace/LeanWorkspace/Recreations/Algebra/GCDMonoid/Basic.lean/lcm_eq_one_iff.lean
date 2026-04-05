import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem lcm_eq_one_iff [NormalizedGCDMonoid α] (a b : α) : lcm a b = 1 ↔ a ∣ 1 ∧ b ∣ 1 := Iff.intro (fun eq => eq ▸ ⟨dvd_lcm_left _ _, dvd_lcm_right _ _⟩) fun ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ =>
    show lcm (Units.mkOfMulEqOne a c hc.symm : α) (Units.mkOfMulEqOne b d hd.symm) = 1 by
      rw [lcm_units_coe_left, normalize_coe_units]

