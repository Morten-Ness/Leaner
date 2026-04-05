import Mathlib

section

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

theorem extendScalars_δ (M₁ M₂ : ModuleCat R) :
    letI := f.toAlgebra
    dsimp% δ (extendScalars f) M₁ M₂ =
      (AlgebraTensorModule.distribBaseChange R S M₁ M₂).toModuleIso.hom :=
  rfl

end

section

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

theorem extendScalars_δ_tmul (M₁ M₂ : ModuleCat R) (m₁ : M₁) (m₂ : M₂) :
    letI := f.toAlgebra
    dsimp% δ (extendScalars f) M₁ M₂ (((1 : S) ⊗ₜ[R] (m₁ ⊗ₜ[R] m₂) :)) =
      ((1 : S) ⊗ₜ[R] m₁) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m₂) := rfl

noncomputable instance : (restrictScalars f).LaxMonoidal :=
  (extendRestrictScalarsAdj f).rightAdjointLaxMonoidal

end

section

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

theorem extendScalars_ε :
    letI := f.toAlgebra
    dsimp% ε (extendScalars f) = (AlgebraTensorModule.rid R S S).toModuleIso.inv := rfl

end

section

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

theorem extendScalars_η :
    letI := f.toAlgebra
    dsimp% η (extendScalars f) = (AlgebraTensorModule.rid R S S).toModuleIso.hom := rfl

end

section

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

theorem extendScalars_μ (M₁ M₂ : ModuleCat R) :
    letI := f.toAlgebra
    dsimp% μ (extendScalars f) M₁ M₂ =
      (AlgebraTensorModule.distribBaseChange R S M₁ M₂).toModuleIso.inv :=
  rfl

end

section

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

theorem extendsScalars_map_leftUnitor_inv_one_tmul (M : ModuleCat R) (m : M) :
    letI := f.toAlgebra
    (extendScalars f).map (λ_ M).inv ((1 : S) ⊗ₜ[R] m) = (1 : S) ⊗ₜ[R] (1 ⊗ₜ m) := rfl

end

section

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

theorem extendsScalars_map_rightUnitor_inv_one_tmul (M : ModuleCat R) (m : M) :
    letI := f.toAlgebra
    (extendScalars f).map (ρ_ M).inv ((1 : S) ⊗ₜ[R] m) = (1 : S) ⊗ₜ[R] (m ⊗ₜ 1) := rfl

end

section

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

theorem restrictScalars_η (r : R) :
    ε (restrictScalars f) r = f r := by
  letI := f.toAlgebra
  dsimp [Adjunction.rightAdjointLaxMonoidal_ε]
  rw [extendRestrictScalarsAdj_homEquiv_apply, ModuleCat.extendScalars_η]
  erw [AlgebraTensorModule.rid_tmul]
  rw [RingHom.smul_toAlgebra, mul_one]

end

section

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

set_option backward.isDefEq.respectTransparency false in
theorem restrictScalars_μ_tmul (M₁ M₂ : ModuleCat S) (m₁ : M₁) (m₂ : M₂) :
    dsimp% μ (restrictScalars f) M₁ M₂ (m₁ ⊗ₜ m₂) = m₁ ⊗ₜ m₂ := by
  dsimp [Adjunction.rightAdjointLaxMonoidal_μ]
  rw [extendRestrictScalarsAdj_homEquiv_apply]
  dsimp
  rw [ModuleCat.extendScalars_δ_tmul, tensorHom_tmul,
    extendRestrictScalarsAdj_counit_app_apply_one_tmul,
    extendRestrictScalarsAdj_counit_app_apply_one_tmul]

end
