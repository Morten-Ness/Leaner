import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem torsionBy_isTorsion_nonZeroDivisor (ha : a ∈ nonZeroDivisors R) :
    IsTorsion R (Submodule.torsionBy R M a) := (⟨⟨a, ha⟩, Submodule.smul_torsionBy _ ·⟩)

