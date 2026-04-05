import Mathlib

variable (α : Type*) [Mul α]

theorem toEquiv_ofLexMulEquiv : (ofLexMulEquiv α : Lex α ≃ α) = ofLex := rfl

