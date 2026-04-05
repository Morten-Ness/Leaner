import Mathlib

variable {R A : Type*} [CommSemiring R] [StarRing R] [Semiring A]

variable [StarMul A] [Algebra R A] [StarModule R A]

theorem isSelfAdjoint_algebraMap_iff {r : R} (h : Function.Injective (algebraMap R A)) :
    IsSelfAdjoint (algebraMap R A r) ↔ IsSelfAdjoint r := ⟨fun hr ↦ h <| algebraMap_star_comm r (A := A) ▸ hr.star_eq, IsSelfAdjoint.algebraMap A⟩

