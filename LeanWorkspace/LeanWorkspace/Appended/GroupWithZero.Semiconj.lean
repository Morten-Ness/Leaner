import Mathlib

section

variable {G₀ : Type*}

variable [GroupWithZero G₀] {a x y x' y' : G₀}

theorem inv_right_iff₀ : SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y := ⟨fun h => inv_inv x ▸ inv_inv y ▸ SemiconjBy.inv_right₀ h, SemiconjBy.inv_right₀⟩

end

section

variable {G₀ : Type*}

variable [GroupWithZero G₀] {a b : G₀}

theorem self_zpow₀ (a : G₀) (n : ℤ) : Commute a (a ^ n) := Commute.zpow_right₀ (Commute.refl a) n

end

section

variable {G₀ : Type*}

theorem zero_left [MulZeroClass G₀] (x y : G₀) : SemiconjBy 0 x y := by
  simp only [SemiconjBy, mul_zero, zero_mul]

end

section

variable {G₀ : Type*}

theorem zero_right [MulZeroClass G₀] (a : G₀) : SemiconjBy a 0 0 := by
  simp only [SemiconjBy, mul_zero, zero_mul]

end

section

variable {G₀ : Type*}

variable [GroupWithZero G₀] {a b : G₀}

theorem zpow_left₀ (h : Commute a b) (m : ℤ) : Commute (a ^ m) b := (Commute.zpow_right₀ h.symm m).symm

end

section

variable {G₀ : Type*}

variable [GroupWithZero G₀] {a b : G₀}

theorem zpow_self₀ (a : G₀) (n : ℤ) : Commute (a ^ n) a := Commute.zpow_left₀ (Commute.refl a) n

end

section

variable {G₀ : Type*}

variable [GroupWithZero G₀] {a b : G₀}

theorem zpow_zpow_self₀ (a : G₀) (m n : ℤ) : Commute (a ^ m) (a ^ n) := Commute.zpow_zpow₀ (Commute.refl a) m n

end

section

variable {G₀ : Type*}

variable [GroupWithZero G₀] {a b : G₀}

theorem zpow_zpow₀ (h : Commute a b) (m n : ℤ) : Commute (a ^ m) (b ^ n) := Commute.zpow_right₀ (Commute.zpow_left₀ h m) n

end
