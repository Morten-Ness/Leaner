import Mathlib

variable (K : Type*) [NormedField K] {E F : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] (L : Submodule ℤ E)

theorem ZLattice.comap_equiv_apply (e : F ≃ₗ[K] E) (x : L) :
    ZLattice.comap_equiv K L e x = e.symm x := rfl

