import Mathlib

variable {α : Type*}

set_option linter.existingAttributeWarning false in
theorem unsym_inv [Inv α] (a : αˢʸᵐ) : SymAlg.unsym a⁻¹ = (SymAlg.unsym a)⁻¹ := rfl

