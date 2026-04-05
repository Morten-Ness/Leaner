import Mathlib

variable (R : Type u) [CommRing R]

theorem Algebra.FiniteType.exists_fgAlgCatSkeleton (A : Type v) [CommRing A] [Algebra R A]
    [h : Algebra.FiniteType R A] :
    ∃ (P : FGAlgCatSkeleton R), Nonempty (A ≃ₐ[R] P.eval.obj) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp h
  exact ⟨⟨n, RingHom.ker f⟩, ⟨(Ideal.quotientKerAlgEquivOfSurjective hf).symm⟩⟩

