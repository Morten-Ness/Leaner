import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

set_option backward.isDefEq.respectTransparency false in
theorem hahnEmbedding_isOrderedModule [IsOrderedAddMonoid R] [Archimedean R]
    [h : Nonempty (HahnEmbedding.Seed K M R)] :
    ∃ f : M →ₗ[K] Lex R⟦FiniteArchimedeanClass M⟧, StrictMono f ∧
      ∀ (a : M), .mk a = FiniteArchimedeanClass.withTopOrderIso M (ofLex (f a)).orderTop := by
  obtain ⟨e, hdomain⟩ := HahnEmbedding.Partial.exists_domain_eq_top h.some
  obtain harch := HahnEmbedding.Partial.orderTop_eq_archimedeanClassMk e
  obtain ⟨⟨fdomain, f⟩, hpartial⟩ := e
  obtain rfl := hdomain
  refine ⟨f ∘ₗ LinearMap.id.codRestrict ⊤ (by simp), ?_, ?_⟩
  · apply hpartial.strictMono.comp
    intro _ _ h
    simpa [← Subtype.coe_lt_coe] using h
  · simp_rw [LinearPMap.mk_apply] at harch
    simp [harch]

