import Mathlib

variable {α : Type*}

set_option linter.existingAttributeWarning false in
theorem sym_inv [Inv α] (a : α) : SymAlg.sym a⁻¹ = (SymAlg.sym a)⁻¹ := rfl

