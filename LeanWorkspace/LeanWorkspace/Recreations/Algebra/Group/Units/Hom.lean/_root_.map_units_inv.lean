import Mathlib

variable {M : Type u} {N : Type v} {P : Type w} [Monoid M] [Monoid N] [Monoid P]

variable {α : Type*} [DivisionMonoid α]

theorem _root_.map_units_inv {F : Type*} [FunLike F M α] [MonoidHomClass F M α]
    (f : F) (u : Units M) :
    f ↑u⁻¹ = (f u)⁻¹ := ((f : M →* α).comp (Units.coeHom M)).map_inv u

