import Mathlib

theorem sum_range_le_sum {s : Finset ℤ} {c : ℤ} (hs : ∀ x ∈ s, c ≤ x) :
    ∑ n ∈ range #s, (c + n) ≤ ∑ x ∈ s, x := by
  convert Finset.sum_Ico_le_sum hs
  refine sum_nbij (c + ·) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro x mx; rw [mem_Ico]; dsimp only; rw [mem_range] at mx; lia
  · intro x mx y my (h : c + x = c + y); lia
  · intro x mx; simp_rw [coe_range, Set.mem_image, Set.mem_Iio]
    rw [mem_coe, mem_Ico] at mx
    use (x - c).toNat; grind

