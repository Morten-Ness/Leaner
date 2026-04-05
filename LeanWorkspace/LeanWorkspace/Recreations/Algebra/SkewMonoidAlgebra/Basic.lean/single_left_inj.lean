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

theorem single_left_inj {a a' : G} {b : k} (h : b ≠ 0) : SkewMonoidAlgebra.single a b = SkewMonoidAlgebra.single a' b ↔ a = a' := by
  rw [← SkewMonoidAlgebra.toFinsupp_inj]
  exact Finsupp.single_left_inj h

