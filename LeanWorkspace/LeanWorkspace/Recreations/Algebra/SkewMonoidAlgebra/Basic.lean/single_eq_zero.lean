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

theorem single_eq_zero {a : G} {b : k} : SkewMonoidAlgebra.single a b = 0 ↔ b = 0 := by
  simp [← SkewMonoidAlgebra.toFinsupp_inj]

set_option linter.style.whitespace false in -- manual alignment is not recognised

