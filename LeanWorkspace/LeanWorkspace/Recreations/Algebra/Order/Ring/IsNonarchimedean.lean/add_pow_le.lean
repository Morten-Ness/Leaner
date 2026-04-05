import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] {a b : R} {m n : ℕ}

theorem add_pow_le {F α : Type*} [CommRing α] [FunLike F α R] [ZeroHomClass F α R]
    [NonnegHomClass F α R] [SubmultiplicativeHomClass F α R] {f : F} (hna : IsNonarchimedean f)
    (n : ℕ) (a b : α) : ∃ m < n + 1, f ((a + b) ^ n) ≤ f (a ^ m) * f (b ^ (n - m)) := by
  obtain ⟨m, hm_lt, hM⟩ := IsNonarchimedean.finset_image_add hna
    (fun m => a ^ m * b ^ (n - m) * ↑(n.choose m)) (Finset.range (n + 1))
  simp only [Finset.nonempty_range_iff, ne_eq, Nat.succ_ne_zero, not_false_iff, Finset.mem_range,
    forall_true_left] at hm_lt
  refine ⟨m, hm_lt, ?_⟩
  simp only [← add_pow] at hM
  rw [mul_comm] at hM
  exact le_trans hM (le_trans (IsNonarchimedean.nmul_le hna) (map_mul_le_mul _ _ _))

