import Mathlib

variable (K : Type*) [NormedField K] {E F : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] (L : Submodule ℤ E)

theorem ZLattice.coe_comap (e : F →ₗ[K] E) :
    (ZLattice.comap K L e : Set F) = e ⁻¹' L := rfl

