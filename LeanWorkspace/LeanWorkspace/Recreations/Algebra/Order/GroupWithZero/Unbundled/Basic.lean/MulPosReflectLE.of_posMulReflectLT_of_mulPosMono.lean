import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] {a b c : G₀}

theorem MulPosReflectLE.of_posMulReflectLT_of_mulPosMono [MulPosMono G₀] : MulPosReflectLE G₀ where
  elim := by
    rintro ⟨a, ha⟩ b c h
    simpa [ha.ne'] using mul_le_mul_of_nonneg_right h (inv_nonneg.2 ha.le)

attribute [local instance] PosMulReflectLT.toPosMulStrictMono PosMulReflectLT.toPosMulReflectLE

