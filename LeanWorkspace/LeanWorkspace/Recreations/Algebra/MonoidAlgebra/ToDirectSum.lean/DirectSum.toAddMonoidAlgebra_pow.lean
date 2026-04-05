import Mathlib

open scoped DirectSum

variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

theorem DirectSum.toAddMonoidAlgebra_pow [DecidableEq ι] [AddMonoid ι] [Semiring M]
    [∀ m : M, Decidable (m ≠ 0)] (f : ⨁ _ : ι, M) (n : ℕ) :
    (f ^ n).toAddMonoidAlgebra = toAddMonoidAlgebra f ^ n := by
  classical exact map_pow addMonoidAlgebraRingEquivDirectSum.symm f n

