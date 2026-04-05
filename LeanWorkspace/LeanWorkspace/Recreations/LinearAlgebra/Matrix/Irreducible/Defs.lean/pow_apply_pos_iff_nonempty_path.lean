import Mathlib

variable {n R : Type*} [Ring R] [LinearOrder R]

variable {A : Matrix n n R}

theorem pow_apply_pos_iff_nonempty_path
    [Fintype n] [IsOrderedRing R] [PosMulStrictMono R] [Nontrivial R] [DecidableEq n]
    (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) (i j : n) :
    letI := Matrix.toQuiver A
    0 < (A ^ k) i j ↔ Nonempty {p : Path i j // p.length = k} := by
  letI := Matrix.toQuiver A
  induction k generalizing i j with
  | zero =>
    refine ⟨fun h_pos ↦ ?_, fun ⟨p, hp⟩ ↦ ?_⟩
    · rcases eq_or_ne i j with rfl | h_eq
      · exact ⟨⟨Quiver.Path.nil, rfl⟩⟩
      · simp_all
    · simp [Quiver.Path.eq_of_length_zero p hp]
  | succ m ih =>
    rw [pow_succ, mul_apply]
    constructor
    · intro h_pos
      obtain ⟨l, hl_mem, hl_pos⟩ :
          ∃ l ∈ (Finset.univ : Finset n), 0 < (A ^ m) i l * A l j := by
        simpa [Finset.sum_pos_iff_of_nonneg
                 (fun x _ => mul_nonneg (pow_apply_nonneg hA m i x) (hA x j))]
          using h_pos
      have hAm_nonneg : 0 ≤ (A ^ m) i l := pow_apply_nonneg hA m i l
      have hA_nonneg' : 0 ≤ A l j := hA l j
      have h_Am : 0 < (A ^ m) i l := by by_contra! h; simp [le_antisymm h hAm_nonneg] at hl_pos
      have h_A : 0 < A l j := by by_contra! h; simp [le_antisymm h hA_nonneg'] at hl_pos
      obtain ⟨⟨p, rfl⟩⟩ := (ih i l).mp h_Am
      exact ⟨p.cons (PLift.up h_A), by simp⟩
    · rintro ⟨p, hp_len⟩
      cases p with
      | nil => simp [Quiver.Path.length] at hp_len
      | @cons b _ q e =>
        simp only [Quiver.Path.length_cons, Nat.succ.injEq] at hp_len
        have h_Am_pos : 0 < (A ^ m) i b := (ih i b).mpr ⟨q, hp_len⟩
        let h_A_pos := e
        have h_prod : 0 < (A ^ m) i b * A b j := mul_pos h_Am_pos h_A_pos.down
        exact
          (Finset.sum_pos_iff_of_nonneg
            (fun x _ => mul_nonneg (pow_apply_nonneg hA m i x) (hA x j))).2
            ⟨b, Finset.mem_univ b, h_prod⟩

