import Mathlib

variable {k G : Type*}

variable [AddMonoid k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem coeff_single_apply {a a' : G} {b : k} [Decidable (a = a')] :
    SkewMonoidAlgebra.coeff (SkewMonoidAlgebra.single a b) a' = if a = a' then b else 0 := by
  simp [SkewMonoidAlgebra.coeff, Finsupp.single_apply]

