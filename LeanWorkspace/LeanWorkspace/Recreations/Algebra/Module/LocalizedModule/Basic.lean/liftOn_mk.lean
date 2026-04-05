import Mathlib

variable {R : Type u} [CommSemiring R] (S : Submonoid R)

variable (M : Type v) [AddCommMonoid M] [Module R M]

variable (T : Type*) [CommSemiring T] [Algebra R T] [IsLocalization S T]

private theorem example_localization_eq_localizedModule
    {R} [CommSemiring R] (S : Submonoid R) : Localization S = LocalizedModule S R := by
  with_reducible rfl


theorem liftOn_mk {α : Type*} {f : M × S → α} (wd : ∀ (p p' : M × S), p ≈ p' → f p = f p')
    (m : M) (s : S) : LocalizedModule.liftOn (LocalizedModule.mk m s) f wd = f ⟨m, s⟩ := by convert Quotient.liftOn_mk f wd ⟨m, s⟩

