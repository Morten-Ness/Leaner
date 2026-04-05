import Mathlib

variable {R : Type u} [CommSemiring R] (S : Submonoid R)

variable (M : Type v) [AddCommMonoid M] [Module R M]

variable (T : Type*) [CommSemiring T] [Algebra R T] [IsLocalization S T]

private theorem example_localization_eq_localizedModule
    {R} [CommSemiring R] (S : Submonoid R) : Localization S = LocalizedModule S R := by
  with_reducible rfl


theorem mk_add_mk {m1 m2 : M} {s1 s2 : S} :
    LocalizedModule.mk m1 s1 + LocalizedModule.mk m2 s2 = LocalizedModule.mk (s2 • m1 + s1 • m2) (s1 * s2) := by
  simp [LocalizedModule.mk, OreLocalization.oreDiv_add_oreDiv, mul_comm s1 s2, Submonoid.smul_def]

