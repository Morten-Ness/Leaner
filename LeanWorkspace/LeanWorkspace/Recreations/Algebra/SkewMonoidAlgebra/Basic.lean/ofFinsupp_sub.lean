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

theorem ofFinsupp_sub {a b} : (⟨a - b⟩ : SkewMonoidAlgebra k G) = ⟨a⟩ - ⟨b⟩ := SkewMonoidAlgebra.toFinsuppAddEquiv.symm.map_sub a b

