import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

theorem smul_expect {G : Type*} [DistribSMul G M] [SMulCommClass G ℚ≥0 M] (a : G)
    (s : Finset ι) (f : ι → M) : a • 𝔼 i ∈ s, f i = 𝔼 i ∈ s, a • f i := by
  simp only [expect, smul_sum, smul_comm]

