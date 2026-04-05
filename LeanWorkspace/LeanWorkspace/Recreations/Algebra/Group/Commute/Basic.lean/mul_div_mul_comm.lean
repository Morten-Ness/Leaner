import Mathlib

variable {G : Type*}

variable [DivisionMonoid G] {a b c d : G}

theorem mul_div_mul_comm (hcd : Commute c d) (hbc : Commute b c⁻¹) :
    a * b / (c * d) = a / c * (b / d) := (Commute.div_mul_div_comm hcd hbc.symm).symm

