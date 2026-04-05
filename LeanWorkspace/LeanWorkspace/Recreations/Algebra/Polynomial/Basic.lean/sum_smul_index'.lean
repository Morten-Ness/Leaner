import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem sum_smul_index' {S T : Type*} [DistribSMul T R] [AddCommMonoid S] (p : R[X]) (b : T)
    (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0) : (b • p).sum f = p.sum fun n a => f n (b • a) := Finsupp.sum_smul_index' hf

