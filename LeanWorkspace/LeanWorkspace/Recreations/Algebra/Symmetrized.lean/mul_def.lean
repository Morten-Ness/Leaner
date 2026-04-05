import Mathlib

variable {α : Type*}

theorem mul_def [Add α] [Mul α] [One α] [OfNat α 2] [Invertible (2 : α)] (a b : αˢʸᵐ) :
    a * b = SymAlg.sym (⅟2 * (SymAlg.unsym a * SymAlg.unsym b + SymAlg.unsym b * SymAlg.unsym a)) := rfl

