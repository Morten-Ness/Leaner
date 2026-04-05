import Mathlib

variable {k G : Type*}

variable [AddCommMonoid k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem sum_def {N : Type*} [AddCommMonoid N] (f : SkewMonoidAlgebra k G) (g : G → k → N) :
    SkewMonoidAlgebra.sum f g = f.toFinsupp.sum g := rfl

