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

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem ofFinsupp_zero : (⟨0⟩ : SkewMonoidAlgebra k G) = 0 := rfl

