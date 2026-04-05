import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable (K L : CochainComplex C ℤ) (n m p : ℤ)

set_option backward.isDefEq.respectTransparency false in
theorem toHom_mk_eq_zero_iff (x : Cocycle K L n) :
    CochainComplex.HomComplex.CohomologyClass.toHom (CochainComplex.HomComplex.CohomologyClass.mk x) = 0 ↔ x ∈ CochainComplex.HomComplex.coboundaries K L n := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [CochainComplex.HomComplex.coboundaries, exists_prop, AddSubgroup.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
    rw [CochainComplex.HomComplex.CohomologyClass.toHom_mk, HomotopyCategory.quotient_map_eq_zero_iff] at h
    obtain ⟨γ, h⟩ := Cochain.equivHomotopy _ _ h.some
    simp only [Cochain.ofHom_zero, add_zero, Cocycle.equivHomShift_symm_apply,
      Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.rightShift_coe] at h
    exact ⟨n - 1, by simp, n.negOnePow • γ.rightUnshift _ (by lia),
      by simp [Cochain.δ_rightUnshift _ _ _ _ _ (zero_add n), smul_smul, ← h]⟩
  · rw [← CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff] at h
    rw [h, map_zero]

