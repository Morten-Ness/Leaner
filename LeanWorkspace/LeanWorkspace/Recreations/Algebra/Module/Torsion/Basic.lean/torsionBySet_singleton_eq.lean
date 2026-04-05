import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem torsionBySet_singleton_eq : Submodule.torsionBySet R M {a} = Submodule.torsionBy R M a := by
  ext x
  simp only [Submodule.mem_torsionBySet_iff, SetCoe.forall, Set.mem_singleton_iff, forall_eq,
    Submodule.mem_torsionBy_iff]

