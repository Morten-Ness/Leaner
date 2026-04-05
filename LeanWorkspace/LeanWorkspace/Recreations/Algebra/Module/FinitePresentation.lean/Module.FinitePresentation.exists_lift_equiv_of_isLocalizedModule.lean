import Mathlib

variable {R M N N'} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

variable [AddCommGroup N'] [Module R N'] (S : Submonoid R) (f : N →ₗ[R] N') [IsLocalizedModule S f]

variable {M' : Type*} [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M') [IsLocalizedModule S f]

variable {N' : Type*} [AddCommGroup N'] [Module R N'] (g : N →ₗ[R] N') [IsLocalizedModule S g]

theorem Module.FinitePresentation.exists_lift_equiv_of_isLocalizedModule
    [Module.FinitePresentation R M] [Module.FinitePresentation R N]
    (l : M' ≃ₗ[R] N') :
    ∃ (r : R) (hr : r ∈ S)
      (l' : LocalizedModule (.powers r) M ≃ₗ[Localization (.powers r)]
        LocalizedModule (.powers r) N),
      (LocalizedModule.lift (.powers r) g fun s ↦ map_units g ⟨s.1, SetLike.le_def.mp
        (Submonoid.powers_le.mpr hr) s.2⟩) ∘ₗ l'.toLinearMap =
        l ∘ₗ (LocalizedModule.lift (.powers r) f fun s ↦ map_units f ⟨s.1, SetLike.le_def.mp
        (Submonoid.powers_le.mpr hr) s.2⟩) := by
  obtain ⟨l', s, H⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule S g (l ∘ₗ f)
  have : Function.Bijective (IsLocalizedModule.map S f g l') := by
    have : IsLocalizedModule.map S f g l' = (s • LinearMap.id) ∘ₗ l := by
      apply IsLocalizedModule.ext S f (IsLocalizedModule.map_units g)
      apply LinearMap.ext fun x ↦ ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, IsLocalizedModule.map_apply]
      rw [← LinearMap.comp_apply, H]
      simp
    rw [this]
    exact ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units g s)).comp l.bijective
  obtain ⟨r, hr, hr'⟩ := exists_bijective_map_powers S f g _ this
  let rs : Submonoid R := (.powers <| r * s)
  let Rᵣₛ := Localization rs
  have hsu : IsUnit (algebraMap R Rᵣₛ s) := isUnit_of_dvd_unit
      (hu := IsLocalization.map_units (M := rs) Rᵣₛ ⟨_, Submonoid.mem_powers _⟩)
      (map_dvd (algebraMap R Rᵣₛ) ⟨r, mul_comm _ _⟩)
  have : Function.Bijective ((hsu.unit⁻¹).1 • LocalizedModule.map rs l') :=
    ((Module.End.isUnit_iff _).mp ((hsu.unit⁻¹).isUnit.map (algebraMap _ (End Rᵣₛ
      (LocalizedModule rs N))))).comp (hr' (r * s) (dvd_mul_right _ _))
  refine ⟨r * s, mul_mem hr s.2, LinearEquiv.ofBijective _ this, ?_⟩
  apply IsLocalizedModule.ext rs (LocalizedModule.mkLinearMap rs M) fun x ↦ map_units g
    ⟨x.1, SetLike.le_def.mp (Submonoid.powers_le.mpr (mul_mem hr s.2)) x.2⟩
  ext x
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units g s)).1
  have : ∀ x, g (l' x) = s.1 • (l (f x)) := LinearMap.congr_fun H
  simp only [rs, LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    Function.comp_apply, LocalizedModule.mkLinearMap_apply, LinearEquiv.ofBijective_apply,
    LinearMap.smul_apply, LocalizedModule.map_mk, algebraMap_end_apply]
  rw [← map_smul, ← smul_assoc, Algebra.smul_def s.1, hsu.mul_val_inv, one_smul]
  simp only [LocalizedModule.lift_mk, OneMemClass.coe_one, map_one, IsUnit.unit_one,
    inv_one, Units.val_one, Module.End.one_apply, this]

