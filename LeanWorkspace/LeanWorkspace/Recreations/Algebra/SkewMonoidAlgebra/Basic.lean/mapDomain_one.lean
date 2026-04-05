import Mathlib

variable {k G : Type*}

variable [Semiring k]

variable {α α₂ β F : Type*} [Semiring β] [Monoid α] [Monoid α₂] [FunLike F α α₂]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem mapDomain_one [MonoidHomClass F α α₂] (f : F) :
    (SkewMonoidAlgebra.mapDomain f (1 : SkewMonoidAlgebra β α) : SkewMonoidAlgebra β α₂) =
      (1 : SkewMonoidAlgebra β α₂) := by
  simp_rw [SkewMonoidAlgebra.one_def, SkewMonoidAlgebra.mapDomain_single, map_one]

