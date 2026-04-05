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

theorem support_eq_empty {p} : p.support = ∅ ↔ (p : SkewMonoidAlgebra k G) = 0 := by
  rcases p
  simp only [SkewMonoidAlgebra.support, Finsupp.support_eq_empty, SkewMonoidAlgebra.ofFinsupp_eq_zero]

