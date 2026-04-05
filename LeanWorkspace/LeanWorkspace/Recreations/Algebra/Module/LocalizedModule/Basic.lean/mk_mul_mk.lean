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


theorem mk_mul_mk {A : Type*} [Semiring A] [Algebra R A] {a₁ a₂ : A} {s₁ s₂ : S} :
    LocalizedModule.mk a₁ s₁ * LocalizedModule.mk a₂ s₂ = LocalizedModule.mk (a₁ * a₂) (s₁ * s₂) := by rw [LocalizedModule.mk_mul_mk', mul_comm s₁ s₂]

-- For the instance on `Localization S`, we prefer `OreLocalization.instSemiring`.
-- They are defeq but Lean needs to unfold a bunch to verify it.

