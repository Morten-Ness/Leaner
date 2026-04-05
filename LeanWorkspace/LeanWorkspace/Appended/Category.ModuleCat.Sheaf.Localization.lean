import Mathlib

section

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

variable {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasWeakSheafify J AddCommGrpCat.{v}]

theorem inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms :
    J.W.inverseImage (toPresheaf R₀) = (isomorphisms _).inverseImage (sheafification α) := by
  rw [J.W_eq_inverseImage_isomorphisms]
  ext P Q f
  simp only [inverseImage_iff, isomorphisms.iff,
    ← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf.{v} R)]
  exact (isomorphisms _).arrow_mk_iso_iff
    (((Functor.mapArrowFunctor _ _).mapIso (sheafificationCompToSheaf.{v} α)).app (Arrow.mk f))

end
