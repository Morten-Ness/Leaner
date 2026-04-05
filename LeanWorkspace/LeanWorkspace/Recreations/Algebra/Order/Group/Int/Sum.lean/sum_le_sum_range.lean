import Mathlib

theorem sum_le_sum_range {s : Finset ℤ} {c : ℤ} (hs : ∀ x ∈ s, x ≤ c) :
    ∑ x ∈ s, x ≤ ∑ n ∈ range #s, (c - n) := by
  convert Finset.sum_le_sum_Ioc hs
  refine sum_nbij (c - ·) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro x mx; rw [mem_Ioc]; dsimp only; rw [mem_range] at mx; lia
  · intro x mx y my (h : c - x = c - y); lia
  · intro x mx; simp_rw [coe_range, Set.mem_image, Set.mem_Iio]
    rw [mem_coe, mem_Ioc] at mx
    use (c - x).toNat; grind

