import Mathlib

variable {R : Type u} [CommRing R]

theorem hom_ext {M : ModuleCat.{v} R} {N : ModuleCat.{max u v} R} {n : ℕ}
    {f g : M.exteriorPower n ⟶ N}
    (h : ModuleCat.exteriorPower.mk.postcomp f = ModuleCat.exteriorPower.mk.postcomp g) : f = g := by
  ext : 1
  exact ModuleCat.exteriorPower.linearMap_ext h

