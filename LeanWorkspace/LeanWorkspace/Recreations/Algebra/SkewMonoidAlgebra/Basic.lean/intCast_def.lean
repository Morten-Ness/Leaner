import Mathlib

variable {k G : Type*}

variable [AddGroupWithOne k] [One G]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem intCast_def (z : ℤ) : (z : SkewMonoidAlgebra k G) = SkewMonoidAlgebra.single (1 : G) (z : k) := by
  cases z <;> simp

