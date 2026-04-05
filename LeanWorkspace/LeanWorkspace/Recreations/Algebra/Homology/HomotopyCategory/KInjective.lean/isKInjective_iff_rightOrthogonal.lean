import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

theorem isKInjective_iff_rightOrthogonal (L : CochainComplex C ℤ) :
    L.IsKInjective ↔
      (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
        ((HomotopyCategory.quotient _ _).obj L) := by
  refine ⟨fun _ K f hK ↦ ?_,
      fun hL ↦ ⟨fun {K} f hK ↦ ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩⟩
  · obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK
    rw [HomotopyCategory.eq_of_homotopy f 0 (IsKInjective.homotopyZero f hK), Functor.map_zero]
  · rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hK
    rw [hL ((HomotopyCategory.quotient _ _).map f) hK, Functor.map_zero]

