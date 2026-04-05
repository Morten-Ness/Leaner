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


theorem mk_smul_mk (LocalizedModule.r : R) (m : M) (s t : S) :
    Localization.mk LocalizedModule.r s • LocalizedModule.mk m t = LocalizedModule.mk (LocalizedModule.r • m) (s * t) := (OreLocalization.oreDiv_smul_char _ _ _ _ _ _ (mul_comm _ _)).trans (by rw [mul_comm])

