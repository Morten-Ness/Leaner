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

theorem coeff_add (p q : SkewMonoidAlgebra k G) (a : G) :
    SkewMonoidAlgebra.coeff (p + q) a = SkewMonoidAlgebra.coeff p a + SkewMonoidAlgebra.coeff q a := by
  rcases p
  rcases q
  simp_rw [← SkewMonoidAlgebra.ofFinsupp_add, SkewMonoidAlgebra.coeff]
  exact Finsupp.add_apply _ _ _

