import Mathlib

variable (M : Type*) [Monoid M]

variable {R' : Type*} [Ring R'] [MulSemiringAction M R']

variable (U : Subring R') [IsInvariantSubring M U]

theorem IsInvariantSubring.coe_subtypeHom :
    (IsInvariantSubring.subtypeHom M U : U → R') = Subtype.val := rfl

