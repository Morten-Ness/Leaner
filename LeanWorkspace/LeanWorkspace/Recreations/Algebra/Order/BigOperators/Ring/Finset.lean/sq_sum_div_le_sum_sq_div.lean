import Mathlib

variable {ι R S : Type*}

theorem sq_sum_div_le_sum_sq_div [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R] (s : Finset ι)
    (f : ι → R) {g : ι → R} (hg : ∀ i ∈ s, 0 < g i) :
    (∑ i ∈ s, f i) ^ 2 / ∑ i ∈ s, g i ≤ ∑ i ∈ s, f i ^ 2 / g i := by
  have hg' : ∀ i ∈ s, 0 ≤ g i := fun i hi ↦ (hg i hi).le
  have H : ∀ i ∈ s, 0 ≤ f i ^ 2 / g i := fun i hi ↦ div_nonneg (sq_nonneg _) (hg' i hi)
  refine div_le_of_le_mul₀ (sum_nonneg hg') (sum_nonneg H)
    (Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul _ H hg' fun i hi ↦ ?_)
  rw [div_mul_cancel₀]
  exact (hg i hi).ne'

