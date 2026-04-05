import Mathlib

variable {G M R K : Type*}

variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K] {x y ε : K}

variable [ExistsAddOfLE K]

theorem exists_mem_Ico_zpow (hx : 0 < x) (hy : 1 < y) : ∃ n : ℤ, x ∈ Ico (y ^ n) (y ^ (n + 1)) := by
  classical
  have he : ∃ m : ℤ, y ^ m ≤ x := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt x⁻¹ hy
    use -N
    rw [zpow_neg y ↑N, zpow_natCast]
    exact ((inv_lt_comm₀ hx (lt_trans (inv_pos.2 hx) hN)).1 hN).le
  have hb : ∃ b : ℤ, ∀ m, y ^ m ≤ x → m ≤ b := by
    obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt x hy
    refine ⟨M, fun m hm ↦ ?_⟩
    contrapose! hM
    rw [← zpow_natCast]
    exact le_trans (zpow_le_zpow_right₀ hy.le hM.le) hm
  obtain ⟨n, hn₁, hn₂⟩ := Int.exists_greatest_of_bdd hb he
  exact ⟨n, hn₁, lt_of_not_ge fun hge => (Int.lt_succ _).not_ge (hn₂ _ hge)⟩

