import Mathlib

variable {k G : Type*}

variable [Monoid G] [CommSemiring k]

variable {A : Type*} [Semiring A] [Algebra k A]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem coe_algebraMap [MulSemiringAction G A] [SMulCommClass G k A] :
    ⇑(algebraMap k (SkewMonoidAlgebra A G)) = SkewMonoidAlgebra.single 1 ∘ algebraMap k A := rfl

