import Mathlib

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

theorem extendsScalars_map_rightUnitor_inv_one_tmul (M : ModuleCat R) (m : M) :
    letI := f.toAlgebra
    (extendScalars f).map (ρ_ M).inv ((1 : S) ⊗ₜ[R] m) = (1 : S) ⊗ₜ[R] (m ⊗ₜ 1) := rfl

