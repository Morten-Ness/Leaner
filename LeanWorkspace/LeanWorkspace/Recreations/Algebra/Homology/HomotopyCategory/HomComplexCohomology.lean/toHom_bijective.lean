import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable (K L : CochainComplex C ℤ) (n m p : ℤ)

theorem toHom_bijective : Function.Bijective (CochainComplex.HomComplex.CohomologyClass.toHom : CochainComplex.HomComplex.CohomologyClass K L n → _) := by
  refine ⟨fun x y h ↦ ?_, fun f ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := CochainComplex.HomComplex.CohomologyClass.mk_surjective x
    obtain ⟨y, rfl⟩ := CochainComplex.HomComplex.CohomologyClass.mk_surjective y
    rw [← sub_eq_zero, ← CochainComplex.HomComplex.CohomologyClass.mk_sub, CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff, ← CochainComplex.HomComplex.CohomologyClass.toHom_mk_eq_zero_iff,
      CochainComplex.HomComplex.CohomologyClass.mk_sub, map_sub, h, sub_self]
  · obtain ⟨f, rfl⟩ := Functor.map_surjective _ f
    exact ⟨CochainComplex.HomComplex.CohomologyClass.mk (Cocycle.equivHomShift f), by simp [CochainComplex.HomComplex.CohomologyClass.toHom_mk]⟩

