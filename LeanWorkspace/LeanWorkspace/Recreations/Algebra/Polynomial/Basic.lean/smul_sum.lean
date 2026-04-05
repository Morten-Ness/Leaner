import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem smul_sum {S T : Type*} [AddCommMonoid S] [DistribSMul T S] (p : R[X]) (b : T)
    (f : ℕ → R → S) : b • p.sum f = p.sum fun n a => b • f n a := Finsupp.smul_sum

