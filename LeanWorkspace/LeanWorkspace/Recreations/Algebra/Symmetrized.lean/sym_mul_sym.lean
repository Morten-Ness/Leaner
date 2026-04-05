import Mathlib

variable {α : Type*}

theorem sym_mul_sym [Mul α] [Add α] [One α] [OfNat α 2] [Invertible (2 : α)] (a b : α) :
    SymAlg.sym a * SymAlg.sym b = SymAlg.sym (⅟2 * (a * b + b * a)) := rfl

