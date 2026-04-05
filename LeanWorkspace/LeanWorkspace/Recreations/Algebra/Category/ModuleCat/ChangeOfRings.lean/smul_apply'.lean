import Mathlib

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)

variable (M : Type v) [AddCommMonoid M] [Module R M]

theorem smul_apply' (s : S) (g : (ModuleCat.restrictScalars f).obj (of _ S) →ₗ[R] M) (s' : S) :
    (s • g) s' = g (s' * s : S) := rfl

