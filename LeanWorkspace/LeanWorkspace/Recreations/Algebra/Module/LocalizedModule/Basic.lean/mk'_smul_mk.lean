import Mathlib

variable {R : Type u} [CommSemiring R] (S : Submonoid R)

variable (M : Type v) [AddCommMonoid M] [Module R M]

variable (T : Type*) [CommSemiring T] [Algebra R T] [IsLocalization S T]

private theorem example_localization_eq_localizedModule
    {R} [CommSemiring R] (S : Submonoid R) : Localization S = LocalizedModule S R := by
  with_reducible rfl


set_option backward.isDefEq.respectTransparency false in
private theorem example_oreLocalizationInstMonoid_eq_localizedModuleInstMonoid :
    OreLocalization.instMonoid = LocalizedModule.instMonoid (A := R) (S := S) := by
  with_reducible_and_instances rfl


set_option backward.isDefEq.respectTransparency false in
private theorem example_oreLocalizationInstCommRing_eq_localizedModuleInstCommRing
    {R : Type*} [CommRing R] {S : Submonoid R} :
    OreLocalization.instCommRing = (LocalizedModule.instCommRing : CommRing R[S⁻¹]) := by
  with_reducible_and_instances rfl


theorem mk'_smul_mk (LocalizedModule.r : R) (m : M) (s s' : S) :
    IsLocalization.mk' T LocalizedModule.r s • LocalizedModule.mk m s' = LocalizedModule.mk (LocalizedModule.r • m) (s * s') := by
  rw [LocalizedModule.smul_def, LocalizedModule.mk_eq]
  obtain ⟨c, hc⟩ := IsLocalization.eq.mp <| IsLocalization.mk'_sec T (IsLocalization.mk' T LocalizedModule.r s)
  use c
  simp_rw [← mul_smul, Submonoid.smul_def, Submonoid.coe_mul, ← mul_smul, ← mul_assoc,
    mul_comm _ (s' : R), mul_assoc, hc]

