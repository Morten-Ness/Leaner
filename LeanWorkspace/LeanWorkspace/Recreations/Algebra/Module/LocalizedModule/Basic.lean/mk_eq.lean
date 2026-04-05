import Mathlib

variable {R : Type u} [CommSemiring R] (S : Submonoid R)

variable (M : Type v) [AddCommMonoid M] [Module R M]

variable (T : Type*) [CommSemiring T] [Algebra R T] [IsLocalization S T]

private theorem example_localization_eq_localizedModule
    {R} [CommSemiring R] (S : Submonoid R) : Localization S = LocalizedModule S R := by
  with_reducible rfl


theorem mk_eq {m m' : M} {s s' : S} : LocalizedModule.mk m s = LocalizedModule.mk m' s' ↔ ∃ u : S, u • s' • m = u • s • m' := by
  rw [LocalizedModule.mk, LocalizedModule.mk, OreLocalization.oreDiv_eq_iff]
  exact congr($(LocalizedModule.oreEqv_eq_r S M) ⟨m, s⟩ ⟨m', s'⟩)

