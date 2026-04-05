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

theorem coeff_single (a : G) (b : k) [DecidableEq G] :
    SkewMonoidAlgebra.coeff (SkewMonoidAlgebra.single a b) = Pi.single a b := by
  simp [SkewMonoidAlgebra.coeff, Finsupp.single_eq_pi_single]

