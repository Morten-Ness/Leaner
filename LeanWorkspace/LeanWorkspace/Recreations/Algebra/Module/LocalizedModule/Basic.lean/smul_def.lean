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


theorem smul_def (x : T) (m : M) (s : S) :
    x • LocalizedModule.mk m s = LocalizedModule.mk ((IsLocalization.sec S x).1 • m) ((IsLocalization.sec S x).2 * s) := rfl

