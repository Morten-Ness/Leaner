import Mathlib

variable (K : Type*) [NormedField K] {E F : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] (L : Submodule ℤ E)

theorem ZLattice.comap_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace K G]
    (e : F →ₗ[K] E) (e' : G →ₗ[K] F) :
    (ZLattice.comap K (ZLattice.comap K L e) e') = ZLattice.comap K L (e ∘ₗ e') := (Submodule.comap_comp _ _ L).symm

