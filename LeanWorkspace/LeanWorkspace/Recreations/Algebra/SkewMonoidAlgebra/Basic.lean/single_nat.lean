import Mathlib

variable {k G : Type*}

variable [One G] [AddMonoidWithOne k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem single_nat (n : ℕ) : (SkewMonoidAlgebra.single 1 n : SkewMonoidAlgebra k G) = n := (SkewMonoidAlgebra.natCast_def _).symm

