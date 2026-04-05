import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {σ : Type t} [CommRing R] [CommRing S] [Algebra R S]
  (pres : Algebra.Presentation R S ι σ)

set_option backward.isDefEq.respectTransparency false in
theorem surjective_hom₁ : Function.Surjective (Algebra.Presentation.differentials.hom₁ pres) := by
  let φ : (σ →₀ S) →ₗ[pres.Ring] pres.toExtension.Cotangent :=
    { toFun := Algebra.Presentation.differentials.hom₁ pres
      map_add' := by simp
      map_smul' := by simp }
  change Function.Surjective φ
  have h₁ := Algebra.Extension.Cotangent.mk_surjective (P := pres.toExtension)
  have h₂ : Submodule.span pres.Ring
      (Set.range (fun r ↦ (⟨pres.relation r, by simp⟩ : pres.ker))) = ⊤ := by
    refine Submodule.map_injective_of_injective (f := Submodule.subtype pres.ker)
      Subtype.coe_injective ?_
    rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span,
      Submodule.coe_subtype, Ideal.submodule_span_eq]
    simp only [← pres.span_range_relation_eq_ker]
    congr
    aesop
  rw [← LinearMap.range_eq_top] at h₁ ⊢
  rw [← top_le_iff, ← h₁, LinearMap.range_eq_map, ← h₂]
  dsimp
  rw [Submodule.map_span_le]
  rintro _ ⟨r, rfl⟩
  simp only [LinearMap.mem_range]
  refine ⟨Finsupp.single r 1, ?_⟩
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Algebra.Presentation.differentials.hom₁_single, φ]
  rfl

