import Mathlib

section

variable {M₀ M₀' : Type*} [MulZeroOneClass M₀] [Nontrivial M₀]

theorem domain_nontrivial [Zero M₀'] [One M₀'] (f : M₀' → M₀) (zero : f 0 = 0) (one : f 1 = 1) :
    Nontrivial M₀' := ⟨⟨0, 1, mt (congr_arg f) <| by
    rw [zero, one]
    exact zero_ne_one⟩⟩

end

section

variable {M₀ M₀' : Type*} [MulZeroOneClass M₀] [Nontrivial M₀]

variable {G₀ : Type*} [GroupWithZero G₀] {a : G₀}

theorem inv_mul_cancel₀ (h : a ≠ 0) : a⁻¹ * a = 1 := calc
    a⁻¹ * a = a⁻¹ * a * a⁻¹ * a⁻¹⁻¹ := by simp [inv_ne_zero h]
    _ = a⁻¹ * a⁻¹⁻¹ := by simp [h]
    _ = 1 := by simp [inv_ne_zero h]

end

section

variable {M₀ M₀' : Type*} [MulZeroOneClass M₀] [Nontrivial M₀]

variable {G₀ : Type*} [GroupWithZero G₀] {a : G₀}

theorem inv_ne_zero (h : a ≠ 0) : a⁻¹ ≠ 0 := fun a_eq_0 => by
  simpa [a_eq_0] using mul_inv_cancel₀ h

end
