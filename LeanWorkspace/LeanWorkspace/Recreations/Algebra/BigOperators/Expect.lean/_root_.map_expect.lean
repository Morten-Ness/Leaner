import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

theorem _root_.map_expect {F : Type*} [FunLike F M N] [LinearMapClass F ℚ≥0 M N]
    (g : F) (f : ι → M) (s : Finset ι) :
    g (𝔼 i ∈ s, f i) = 𝔼 i ∈ s, g (f i) := by simp only [expect, map_smul, map_sum]

