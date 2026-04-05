import Mathlib

variable {R : Type u} [CommRing R]

variable {M : Type v} [AddCommGroup M] [Module R M] {N : Type v} [AddCommGroup N] [Module R N]

theorem precomp_extClass_surjective_of_projective_X₂ [Small.{v} R]
    (M : ModuleCat.{v} R) {S : ShortComplex (ModuleCat.{v} R)} (h : S.ShortExact) (n : ℕ)
    [Projective S.X₂] : Function.Surjective (h.extClass.precomp M (add_comm 1 n)) := fun x ↦ Ext.contravariant_sequence_exact₃ h M x (Ext.eq_zero_of_projective _) (add_comm 1 n)

