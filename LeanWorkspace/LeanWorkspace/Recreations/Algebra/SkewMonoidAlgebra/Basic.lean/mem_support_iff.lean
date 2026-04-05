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

theorem mem_support_iff {f : SkewMonoidAlgebra k G} {a : G} : a ∈ f.support ↔ f.coeff a ≠ 0 := by
  rcases f with ⟨⟩
  simp only [SkewMonoidAlgebra.coeff, SkewMonoidAlgebra.support_ofFinsupp, Finsupp.mem_support_iff, ne_eq]

