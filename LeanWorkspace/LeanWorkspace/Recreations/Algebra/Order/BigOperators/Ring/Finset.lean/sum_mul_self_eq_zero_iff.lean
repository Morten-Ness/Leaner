import Mathlib

variable {ι R S : Type*}

theorem sum_mul_self_eq_zero_iff [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R] (s : Finset ι)
    (f : ι → R) : ∑ i ∈ s, f i * f i = 0 ↔ ∀ i ∈ s, f i = 0 := by
  rw [sum_eq_zero_iff_of_nonneg fun _ _ ↦ mul_self_nonneg _]
  simp

