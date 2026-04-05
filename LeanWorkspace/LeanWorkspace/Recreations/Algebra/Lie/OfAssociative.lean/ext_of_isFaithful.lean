import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

theorem ext_of_isFaithful [IsFaithful R L M] {x y : L} (h : ∀ m : M, ⁅x, m⁆ = ⁅y, m⁆) :
    x = y := (LieModule.toEnd_eq_iff R L M).mp <| LinearMap.ext h

