import Mathlib

variable {R S : Type*}

variable [CommSemiring R]

variable [PartialOrder R] [AddLeftReflectLE R] [AddLeftMono R] [ExistsAddOfLE R] [Sub R]
  [OrderedSub R] {x y : R}

theorem geom_sum₂_mul_of_le (hxy : x ≤ y) (n : ℕ) :
    (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) * (y - x) = y ^ n - x ^ n := by
  rw [← Finset.sum_range_reflect]
  convert geom_sum₂_mul_of_ge hxy n using 3
  simp_all only [Finset.mem_range]
  rw [mul_comm]
  congr
  lia

