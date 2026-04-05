import Mathlib

variable {R : Type u} [CommSemiring R] (S : Submonoid R)

variable (M : Type v) [AddCommMonoid M] [Module R M]

variable (T : Type*) [CommSemiring T] [Algebra R T] [IsLocalization S T]

private theorem example_localization_eq_localizedModule
    {R} [CommSemiring R] (S : Submonoid R) : Localization S = LocalizedModule S R := by
  with_reducible rfl


theorem subsingleton (h : 0 ∈ S) : Subsingleton (LocalizedModule S M) := by
  refine ⟨fun a b ↦ ?_⟩
  induction a, b using LocalizedModule.induction_on₂
  exact LocalizedModule.mk_eq.mpr ⟨⟨0, h⟩, by simp only [Submonoid.mk_smul, zero_smul]⟩

