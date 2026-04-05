import Mathlib

variable {α : Type*}

theorem invOf_sym [Mul α] [AddMonoidWithOne α] [Invertible (2 : α)] (a : α) [Invertible a] :
    ⅟(SymAlg.sym a) = SymAlg.sym (⅟a) := rfl

