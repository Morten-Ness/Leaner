import Mathlib

variable (K : Type*) [NormedField K] {E F : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] (L : Submodule ℤ E)

theorem ZLattice.comap_toAddSubgroup (e : F →ₗ[K] E) :
    (ZLattice.comap K L e).toAddSubgroup = L.toAddSubgroup.comap e.toAddMonoidHom := rfl

