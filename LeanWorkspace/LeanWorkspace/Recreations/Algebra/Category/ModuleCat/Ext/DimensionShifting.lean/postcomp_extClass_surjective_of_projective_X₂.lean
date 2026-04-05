import Mathlib

variable {R : Type u} [CommRing R]

variable {M : Type v} [AddCommGroup M] [Module R M] {N : Type v} [AddCommGroup N] [Module R N]

theorem postcomp_extClass_surjective_of_projective_X₂ [Small.{v} R]
    {S : ShortComplex (ModuleCat.{v} R)} (h : S.ShortExact) (M : ModuleCat.{v} R) (n : ℕ)
    [Function.Injective S.X₂] : Function.Surjective (h.extClass.postcomp M (rfl : n + 1 = n + 1)) := fun x ↦ Ext.covariant_sequence_exact₁ M h x (Ext.eq_zero_of_injective _) rfl

