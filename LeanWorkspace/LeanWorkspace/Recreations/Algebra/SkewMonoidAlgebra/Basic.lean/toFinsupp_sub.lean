import Mathlib

variable {k G : Type*}

variable [AddGroup k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem toFinsupp_sub (a b : SkewMonoidAlgebra k G) :
    (a - b).toFinsupp = a.toFinsupp - b.toFinsupp := SkewMonoidAlgebra.toFinsuppAddEquiv.map_sub a b

