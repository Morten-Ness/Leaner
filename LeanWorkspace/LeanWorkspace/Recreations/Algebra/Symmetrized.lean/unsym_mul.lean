import Mathlib

variable {α : Type*}

theorem unsym_mul [Mul α] [Add α] [One α] [OfNat α 2] [Invertible (2 : α)] (a b : αˢʸᵐ) :
    SymAlg.unsym (a * b) = ⅟2 * (SymAlg.unsym a * SymAlg.unsym b + SymAlg.unsym b * SymAlg.unsym a) := rfl

