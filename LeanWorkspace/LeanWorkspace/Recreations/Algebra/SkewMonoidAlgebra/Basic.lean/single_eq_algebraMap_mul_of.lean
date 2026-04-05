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

theorem single_eq_algebraMap_mul_of [MulSemiringAction G k] [SMulCommClass G k k] (a : G) (b : k) :
    SkewMonoidAlgebra.single a b = algebraMap k (SkewMonoidAlgebra k G) b * SkewMonoidAlgebra.of k G a := by
  simp [SkewMonoidAlgebra.coe_algebraMap, comp_apply, SkewMonoidAlgebra.of_apply, SkewMonoidAlgebra.single_mul_single, one_mul, smul_one, mul_one]

