import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem coe_mul_of_left_le_normalizer_right (H N : Subgroup G) (hLE : H ≤ normalizer N) :
    (↑(H ⊔ N) : Set G) = H * N := by
  rw [Subgroup.sup_eq_closure_mul]
  refine Set.Subset.antisymm (fun x hx => ?_) subset_closure
  induction hx using Subgroup.closure_induction'' with
  | one => exact ⟨1, one_mem _, 1, one_mem _, mul_one 1⟩
  | mem _ hx => exact hx
  | inv_mem x hx =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hx
    simpa only [mul_inv_rev, mul_assoc, inv_inv, inv_mul_cancel_left]
      using mul_mem_mul (inv_mem hx) ((mem_normalizer_iff.mp (hLE hx) y⁻¹).mp (inv_mem hy))
  | mul x' x' _ _ hx hx' =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hx
    obtain ⟨x', hx', y', hy', rfl⟩ := hx'
    refine ⟨x * x', mul_mem hx hx', x'⁻¹ * y * x' * y', mul_mem ?_ hy', ?_⟩
    · exact (mem_normalizer_iff''.mp (hLE hx') y).mp hy
    · simp only [mul_assoc, mul_inv_cancel_left]

