import Mathlib

variable {R : Type u} [CommRing R] [Small.{v} R]

variable {R' : Type u'} [CommRing R'] [Small.{v'} R'] (e : R ≃+* R')

variable {M : ModuleCat.{v} R} {N : ModuleCat.{v'} R'}

theorem projectiveDimension_eq_of_semiLinearEquiv (e' : M ≃ₛₗ[RingHomClass.toRingHom e] N) :
    projectiveDimension M = projectiveDimension N := by
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot => simpa [projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton] using
      e'.subsingleton_congr
  | coe n =>
    induction n with
    | top => simp
    | coe n =>
      norm_cast
      simp only [projectiveDimension_le_iff]
      exact ⟨fun h ↦ CategoryTheory.hasProjectiveDimensionLE_of_semiLinearEquiv e e' n,
        fun h ↦ CategoryTheory.hasProjectiveDimensionLE_of_semiLinearEquiv e.symm e'.symm n⟩

