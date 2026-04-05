import Mathlib

section

variable (R : Type u) [CommRing R]

theorem Algebra.FiniteType.exists_fgAlgCatSkeleton (A : Type v) [CommRing A] [Algebra R A]
    [h : Algebra.FiniteType R A] :
    ∃ (P : FGAlgCatSkeleton R), Nonempty (A ≃ₐ[R] P.eval.obj) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp h
  exact ⟨⟨n, RingHom.ker f⟩, ⟨(Ideal.quotientKerAlgEquivOfSurjective hf).symm⟩⟩

end

section

variable (R : Type u) [CommRing R]

variable {Q : MorphismProperty CommRingCat.{u}}

theorem essentiallySmall_of_le (hQ : Q ≤ toMorphismProperty FiniteType) (R : CommRingCat.{u}) :
    EssentiallySmall.{u} (MorphismProperty.Under Q ⊤ R) := essentiallySmall_of_fully_faithful
    (MorphismProperty.Comma.changeProp _ _ hQ
      le_rfl le_rfl ⋙ (FGAlgCat.equivUnder R).inverse)

end
