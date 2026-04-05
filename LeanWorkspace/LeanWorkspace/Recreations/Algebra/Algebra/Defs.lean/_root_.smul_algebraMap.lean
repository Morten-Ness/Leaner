import Mathlib

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

variable [CommSemiring R] [CommSemiring S]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem _root_.smul_algebraMap {α : Type*} [Monoid α] [MulDistribMulAction α A]
    [SMulCommClass α R A] (a : α) (r : R) : a • algebraMap R A r = algebraMap R A r := by
  rw [Algebra.algebraMap_eq_smul_one, smul_comm a r (1 : A), smul_one]

