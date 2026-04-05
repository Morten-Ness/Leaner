import Mathlib

section

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

set_option backward.isDefEq.respectTransparency false in
theorem extendScalarsId_hom_app_one_tmul (M : ModuleCat R) (m : M) :
    (ModuleCat.extendScalarsId R).hom.app M ((1 : R) ⊗ₜ m) = m := by
  rw [← ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
    ModuleCat.homEquiv_extendScalarsId]
  dsimp

end

section

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

set_option backward.isDefEq.respectTransparency false in
theorem hom_ext {M : ModuleCat R} {N : ModuleCat S}
    {α β : (ModuleCat.extendScalars f).obj M ⟶ N}
    (h : ∀ (m : M), α ((1 : S) ⊗ₜ m) = β ((1 : S) ⊗ₜ m)) : α = β := by
  apply (ModuleCat.restrictScalars f).map_injective
  letI := f.toAlgebra
  ext : 1
  apply TensorProduct.ext'
  intro (s : S) m
  change α (s ⊗ₜ m) = β (s ⊗ₜ m)
  have : s ⊗ₜ[R] (m : M) = s • (1 : S) ⊗ₜ[R] m := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  simp only [this, map_smul, h]

end
