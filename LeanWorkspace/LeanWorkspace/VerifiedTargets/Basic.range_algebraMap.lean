import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

variable {α β : Type*}

theorem range_algebraMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (S : Subalgebra R A) : (algebraMap S A).range = S.toSubring := by
  rw [Subalgebra.algebraMap_eq, Algebra.algebraMap_self, RingHom.id_comp, ← Subalgebra.toSubring_subtype,
    Subring.range_subtype]

