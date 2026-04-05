import Mathlib

variable {k G : Type*}

variable [One G] [AddMonoidWithOne k]

set_option backward.privateInPublic true in
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩

theorem coeff_one {a : G} [Decidable (a = 1)] :
    (1 : SkewMonoidAlgebra k G).coeff a = if a = 1 then 1 else 0 := by
  classical
  simpa [eq_comm (a := a)] using SkewMonoidAlgebra.coeff_single_apply

