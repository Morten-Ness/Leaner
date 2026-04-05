import Mathlib

variable {R M N N'} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

variable [AddCommGroup N'] [Module R N'] (S : Submonoid R) (f : N →ₗ[R] N') [IsLocalizedModule S f]

variable {M' : Type*} [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M') [IsLocalizedModule S f]

variable {N' : Type*} [AddCommGroup N'] [Module R N'] (g : N →ₗ[R] N') [IsLocalizedModule S g]

theorem exists_bijective_map_powers [Module.Finite R M] [Module.FinitePresentation R N]
    (l : M →ₗ[R] N) (hf : Function.Bijective (IsLocalizedModule.map S f g l)) :
    ∃ r, r ∈ S ∧ ∀ t, r ∣ t → Function.Bijective (LocalizedModule.map (.powers t) l) := by
  let e : M' ≃ₗ[R] N' := LinearEquiv.ofBijective _ hf
  obtain ⟨l', s₀, H⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule S f
    (e.symm.toLinearMap.comp g)
  have H₁ : g ∘ₗ l ∘ₗ l' = g ∘ₗ (s₀ • LinearMap.id) := by
    ext a; simpa [-EmbeddingLike.apply_eq_iff_eq, e] using congr(e ($H a))
  obtain ⟨s₁, hs₁⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule S g _ _ H₁
  have H₂ : f ∘ₗ l' ∘ₗ l = f ∘ₗ (s₀ • LinearMap.id) := by
    rw [← LinearMap.comp_assoc, H, LinearMap.smul_comp, LinearMap.comp_assoc,
      ← IsLocalizedModule.map_comp S f g l, ← LinearMap.comp_assoc]
    change s₀ • (e.symm.toLinearMap ∘ₗ e.toLinearMap) ∘ₗ _ = _
    simp [LinearMap.comp_smul]
  obtain ⟨s₂, hs₂⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule S f _ _ H₂
  refine ⟨s₀ * s₁ * s₂, (s₀ * s₁ * s₂).2, fun t ht ↦ ?_⟩
  let Rₛ := Localization (.powers t)
  let lₛ := LocalizedModule.map (.powers t) l
  have hu := IsLocalization.map_units (M := .powers t) Rₛ ⟨t, Submonoid.mem_powers t⟩
  have hu₀ : IsUnit (algebraMap R Rₛ s₀) := isUnit_of_dvd_unit
      (map_dvd (algebraMap R Rₛ) (dvd_trans ⟨s₁ * s₂, by simp [mul_assoc]⟩ ht)) hu
  have hu₁ : IsUnit (algebraMap R Rₛ s₁) := isUnit_of_dvd_unit
      (map_dvd (algebraMap R Rₛ) (dvd_trans ⟨s₀ * s₂, by ring⟩ ht)) hu
  have hu₂ : IsUnit (algebraMap R Rₛ s₂) := isUnit_of_dvd_unit
      (map_dvd (algebraMap R Rₛ) (dvd_trans ⟨s₀ * s₁, by ring⟩ ht)) hu
  let lₛ' := LocalizedModule.map (.powers t) l'
  have H_left : ((hu₀.unit⁻¹).1 • lₛ') ∘ₗ lₛ = LinearMap.id := by
    apply ((Module.End.isUnit_iff _).mp (hu₂.map (algebraMap Rₛ (Module.End Rₛ _)))).1
    apply ((Module.End.isUnit_iff _).mp (hu₀.map (algebraMap Rₛ (Module.End Rₛ _)))).1
    simp only [Module.algebraMap_end_apply, algebraMap_smul, LinearMap.map_smul_of_tower]
    rw [LinearMap.smul_comp, ← smul_assoc s₀.1, Algebra.smul_def s₀.1, IsUnit.mul_val_inv, one_smul]
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.ext (.powers t) (LocalizedModule.mkLinearMap (.powers t) M)
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (.powers t) M))
    ext x
    have : s₂.1 • l' (l x) = s₂.1 • s₀.1 • x := congr($hs₂ x)
    simp [lₛ, lₛ', LocalizedModule.smul'_mk, this]
  have H_right : lₛ ∘ₗ ((hu₀.unit⁻¹).1 • lₛ') = LinearMap.id := by
    apply ((Module.End.isUnit_iff _).mp (hu₁.map (algebraMap Rₛ (Module.End Rₛ _)))).1
    apply ((Module.End.isUnit_iff _).mp (hu₀.map (algebraMap Rₛ (Module.End Rₛ _)))).1
    simp only [Module.algebraMap_end_apply, algebraMap_smul, LinearMap.map_smul_of_tower]
    rw [LinearMap.comp_smul, ← smul_assoc s₀.1, Algebra.smul_def s₀.1, IsUnit.mul_val_inv, one_smul]
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.ext (.powers t) (LocalizedModule.mkLinearMap (.powers t) N)
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (.powers t) N))
    ext x
    have : s₁.1 • l (l' x) = s₁.1 • s₀.1 • x := congr($hs₁ x)
    simp [lₛ, lₛ', LocalizedModule.smul'_mk, this]
  let eₛ : LocalizedModule (.powers t) M ≃ₗ[Rₛ] LocalizedModule (.powers t) N :=
    { __ := lₛ,
      invFun := ((hu₀.unit⁻¹).1 • lₛ'),
      left_inv := fun x ↦ congr($H_left x),
      right_inv := fun x ↦ congr($H_right x) }
  exact eₛ.bijective

