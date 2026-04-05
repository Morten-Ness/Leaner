import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem modEq_nsmul_cases (n : ℕ) (hn : n ≠ 0) :
    a ≡ b [PMOD p] ↔ ∃ i < n, a ≡ b + i • p [PMOD (n • p)] := by
  simp_rw [← AddCommGroup.sub_modEq_iff_modEq_add, AddCommGroup.modEq_comm (b := b)]
  simp_rw [AddCommGroup.modEq_iff_zsmul', sub_right_comm, sub_eq_iff_eq_add (b := _ • _), ← natCast_zsmul,
    ← mul_zsmul, ← AddCommGroup.ModEq.add_zsmul]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨(k % n).toNat, ?_⟩
    rw [← Int.ofNat_lt, Int.toNat_of_nonneg (Int.emod_nonneg _ (mod_cast hn))]
    refine ⟨?_, k / n, ?_⟩
    · refine Int.emod_lt_of_pos _ ?_
      lia
    · rw [hk, Int.ediv_mul_add_emod]
  · rintro ⟨k, _, j, hj⟩
    rw [hj]
    exact ⟨_, rfl⟩

alias ⟨AddCommGroup.ModEq.nsmul_cases, _⟩ := AddCommGroup.modEq_nsmul_cases

