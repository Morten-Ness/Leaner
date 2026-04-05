import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

theorem isKProjective_iff_leftOrthogonal (K : CochainComplex C ℤ) :
    K.IsKProjective ↔
      (HomotopyCategory.subcategoryAcyclic C).leftOrthogonal
        ((HomotopyCategory.quotient _ _).obj K) := by
  refine ⟨fun _ L f hL ↦ ?_,
      fun hK ↦ ⟨fun {L} f hL ↦ ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩⟩
  · obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hL
    rw [HomotopyCategory.eq_of_homotopy f 0 (IsKProjective.homotopyZero f hL), Functor.map_zero]
  · rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hL
    rw [hK ((HomotopyCategory.quotient _ _).map f) hL, Functor.map_zero]

