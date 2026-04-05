import Mathlib

variable {R : Type u} [CommSemiring R] (S : Submonoid R)

variable (M : Type v) [AddCommMonoid M] [Module R M]

variable (T : Type*) [CommSemiring T] [Algebra R T] [IsLocalization S T]

private theorem example_localization_eq_localizedModule
    {R} [CommSemiring R] (S : Submonoid R) : Localization S = LocalizedModule S R := by
  with_reducible rfl


theorem mk_neg {M : Type*} [AddCommGroup M] [Module R M] {m : M} {s : S} :
    LocalizedModule.mk (-m) s = -LocalizedModule.mk m s := by simp [LocalizedModule.mk]

