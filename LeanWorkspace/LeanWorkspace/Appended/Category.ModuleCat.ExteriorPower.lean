import Mathlib

section

variable {R : Type u} [CommRing R]

theorem desc_mk {M : ModuleCat.{v} R} {n : ℕ} {N : ModuleCat.{max u v} R}
    (φ : M.AlternatingMap N n) (x : Fin n → M) :
    ModuleCat.exteriorPower.desc φ (ModuleCat.exteriorPower.mk x) = φ x := by
  apply ModuleCat.exteriorPower.alternatingMapLinearEquiv_apply_ιMulti

end

section

variable {R : Type u} [CommRing R]

theorem hom_ext {M : ModuleCat.{v} R} {N : ModuleCat.{max u v} R} {n : ℕ}
    {f g : M.exteriorPower n ⟶ N}
    (h : ModuleCat.exteriorPower.mk.postcomp f = ModuleCat.exteriorPower.mk.postcomp g) : f = g := by
  ext : 1
  exact ModuleCat.exteriorPower.linearMap_ext h

end

section

variable {R : Type u} [CommRing R]

theorem iso₀_hom_apply {M : ModuleCat.{u} R} (f : Fin 0 → M) :
    (ModuleCat.exteriorPower.iso₀ M).hom (ModuleCat.exteriorPower.mk f) = 1 := ModuleCat.exteriorPower.zeroEquiv_ιMulti _

end

section

variable {R : Type u} [CommRing R]

theorem iso₀_hom_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ModuleCat.exteriorPower.map f 0 ≫ (ModuleCat.exteriorPower.iso₀ N).hom = (ModuleCat.exteriorPower.iso₀ M).hom := ModuleCat.hom_ext (ModuleCat.exteriorPower.zeroEquiv_naturality f.hom)

end

section

variable {R : Type u} [CommRing R]

theorem iso₁_hom_apply {M : ModuleCat.{u} R} (f : Fin 1 → M) :
    (ModuleCat.exteriorPower.iso₁ M).hom (ModuleCat.exteriorPower.mk f) = f 0 := ModuleCat.exteriorPower.oneEquiv_ιMulti _

end

section

variable {R : Type u} [CommRing R]

theorem iso₁_hom_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ModuleCat.exteriorPower.map f 1 ≫ (ModuleCat.exteriorPower.iso₁ N).hom = (ModuleCat.exteriorPower.iso₁ M).hom ≫ f := ModuleCat.hom_ext (ModuleCat.exteriorPower.oneEquiv_naturality f.hom)

end

section

variable {R : Type u} [CommRing R]

theorem map_mk {M N : ModuleCat.{v} R} (f : M ⟶ N) {n : ℕ} (x : Fin n → M) :
    ModuleCat.exteriorPower.map f n (ModuleCat.exteriorPower.mk x) = ModuleCat.exteriorPower.mk (f ∘ x) := by
  apply ModuleCat.exteriorPower.map_apply_ιMulti

end
