import Mathlib

variable (K : Type*) [NormedField K] {E F : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] (L : Submodule ℤ E)

theorem ZLattice.comap_refl :
    ZLattice.comap K L (1 : E →ₗ[K] E) = L := Submodule.comap_id L

