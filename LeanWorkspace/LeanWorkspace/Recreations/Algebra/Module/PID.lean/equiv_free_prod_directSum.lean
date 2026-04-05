import Mathlib

open scoped DirectSum

variable {R : Type u} [CommRing R] [IsPrincipalIdealRing R]

variable {M : Type v} [AddCommGroup M] [Module R M]

variable [IsDomain R]

theorem equiv_free_prod_directSum [h' : Module.Finite R M] :
    ∃ (n : ℕ) (ι : Type u) (_ : Fintype ι) (p : ι → R) (_ : ∀ i, Irreducible <| p i) (e : ι → ℕ),
      Nonempty <| M ≃ₗ[R] (Fin n →₀ R) × ⨁ i : ι, R ⧸ R ∙ p i ^ e i := by
  obtain ⟨I, fI, p, hp, e, ⟨h⟩⟩ :=
    Module.equiv_directSum_of_isTorsion.{u, v} (@torsion_isTorsion R M _ _ _)
  obtain ⟨n, ⟨g⟩⟩ := @Module.basisOfFiniteTypeTorsionFree' R _ (M ⧸ torsion R M) _ _ _ _ _ _
  obtain ⟨f, hf⟩ := Module.projective_lifting_property _ LinearMap.id (torsion R M).mkQ_surjective
  refine
    ⟨n, I, fI, p, hp, e,
      ⟨(lequivProdOfRightSplitExact (torsion R M).injective_subtype ?_ hf).symm.trans <|
          (h.prodCongr g).trans <| LinearEquiv.prodComm.{u, u} R _ (Fin n →₀ R) ⟩⟩
  rw [range_subtype, ker_mkQ]

