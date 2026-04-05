import Mathlib

variable {R A C : Type*} [CommSemiring R] [NonUnitalSemiring A] [StarRing R] [StarRing A]

variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] [StarModule R A]

variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

theorem starLift_range_le
    {f : A →⋆ₙₐ[R] C} {S : StarSubalgebra R C} :
    (starLift f).range ≤ S ↔ NonUnitalStarAlgHom.range f ≤ S.toNonUnitalStarSubalgebra := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rintro - ⟨x, rfl⟩
    exact @h (f x) ⟨x, by simp⟩
  · rintro - ⟨x, rfl⟩
    induction x with
    | _ r a => simpa using add_mem (algebraMap_mem S r) (h ⟨a, rfl⟩)

