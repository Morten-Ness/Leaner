import Mathlib

variable {R : Type*} [NonAssocRing R] [LinearOrder R] [IsOrderedAddMonoid R] [Archimedean R] {p : R}
  (hp : 0 < p)

private theorem toIxxMod_iff (x₁ x₂ x₃ : α) : toIcoMod hp x₁ x₂ ≤ toIocMod hp x₁ x₃ ↔
    toIcoMod hp 0 (x₂ - x₁) + toIcoMod hp 0 (x₁ - x₃) ≤ p := by
  rw [toIcoMod_eq_sub, toIocMod_eq_sub _ x₁, add_le_add_iff_right, ← neg_sub x₁ x₃, toIocMod_neg,
    neg_zero, le_sub_iff_add_le]


private theorem toIxxMod_cyclic_left {x₁ x₂ x₃ : α} (h : toIcoMod hp x₁ x₂ ≤ toIocMod hp x₁ x₃) :
    toIcoMod hp x₂ x₃ ≤ toIocMod hp x₂ x₁ := by
  let x₂' := toIcoMod hp x₁ x₂
  let x₃' := toIcoMod hp x₂' x₃
  have h : x₂' ≤ toIocMod hp x₁ x₃' := by simpa [x₃']
  have h₂₁ : x₂' < x₁ + p := toIcoMod_lt_right _ _ _
  have h₃₂ : x₃' - p < x₂' := sub_lt_iff_lt_add.2 (toIcoMod_lt_right _ _ _)
  suffices hequiv : x₃' ≤ toIocMod hp x₂' x₁ by
    obtain ⟨z, hd⟩ : ∃ z : ℤ, x₂ = x₂' + z • p := ((toIcoMod_eq_iff hp).1 rfl).2
    simpa [hd, toIocMod_add_zsmul', toIcoMod_add_zsmul', add_le_add_iff_right]
  rcases le_or_gt x₃' (x₁ + p) with h₃₁ | h₁₃
  · suffices hIoc₂₁ : toIocMod hp x₂' x₁ = x₁ + p from hIoc₂₁.trans_ge h₃₁
    apply (toIocMod_eq_iff hp).2
    exact ⟨⟨h₂₁, by simp [x₂', left_le_toIcoMod]⟩, -1, by simp⟩
  have hIoc₁₃ : toIocMod hp x₁ x₃' = x₃' - p := by
    apply (toIocMod_eq_iff hp).2
    exact ⟨⟨lt_sub_iff_add_lt.2 h₁₃, le_of_lt (h₃₂.trans h₂₁)⟩, 1, by simp⟩
  have not_h₃₂ := (h.trans hIoc₁₃.le).not_gt
  contradiction


private theorem toIxxMod_antisymm (h₁₂₃ : toIcoMod hp a b ≤ toIocMod hp a c)
    (h₁₃₂ : toIcoMod hp a c ≤ toIocMod hp a b) :
    b ≡ a [PMOD p] ∨ c ≡ b [PMOD p] ∨ a ≡ c [PMOD p] := by
  by_contra! h
  rw [modEq_comm] at h
  rw [← (AddCommGroup.not_modEq_iff_toIcoMod_eq_toIocMod hp).mp h.2.2] at h₁₂₃
  rw [← (AddCommGroup.not_modEq_iff_toIcoMod_eq_toIocMod hp).mp h.1] at h₁₃₂
  exact h.2.1 ((toIcoMod_inj _).1 <| h₁₃₂.antisymm h₁₂₃)


private theorem toIxxMod_total' (a b c : α) :
    toIcoMod hp b a ≤ toIocMod hp b c ∨ toIcoMod hp b c ≤ toIocMod hp b a := by
  /- an essential ingredient is the lemma saying {a-b} + {b-a} = period if a ≠ b (and = 0 if a = b).
    Thus if a ≠ b and b ≠ c then ({a-b} + {b-c}) + ({c-b} + {b-a}) = 2 * period, so one of
    `{a-b} + {b-c}` and `{c-b} + {b-a}` must be `≤ period` -/
  have := congr_arg₂ (· + ·) (toIcoMod_add_toIocMod_zero hp a b) (toIcoMod_add_toIocMod_zero hp c b)
  simp only [add_add_add_comm] at this
  rw [_root_.add_comm (toIocMod _ _ _), add_add_add_comm, ← two_nsmul] at this
  replace := min_le_of_add_le_two_nsmul this.le
  rw [min_le_iff] at this
  rw [toIxxMod_iff, toIxxMod_iff]
  grw [← toIcoMod_le_toIocMod, ← toIcoMod_le_toIocMod] at this
  exact this


private theorem toIxxMod_total (a b c : α) :
    toIcoMod hp a b ≤ toIocMod hp a c ∨ toIcoMod hp c b ≤ toIocMod hp c a := (toIxxMod_total' _ _ _ _).imp_right <| toIxxMod_cyclic_left _


private theorem toIxxMod_trans {x₁ x₂ x₃ x₄ : α}
    (h₁₂₃ : toIcoMod hp x₁ x₂ ≤ toIocMod hp x₁ x₃ ∧ ¬toIcoMod hp x₃ x₂ ≤ toIocMod hp x₃ x₁)
    (h₂₃₄ : toIcoMod hp x₂ x₄ ≤ toIocMod hp x₂ x₃ ∧ ¬toIcoMod hp x₃ x₄ ≤ toIocMod hp x₃ x₂) :
    toIcoMod hp x₁ x₄ ≤ toIocMod hp x₁ x₃ ∧ ¬toIcoMod hp x₃ x₄ ≤ toIocMod hp x₃ x₁ := by
  constructor
  · suffices h : ¬x₃ ≡ x₂ [PMOD p] by
      have h₁₂₃' := toIxxMod_cyclic_left _ (toIxxMod_cyclic_left _ h₁₂₃.1)
      have h₂₃₄' := toIxxMod_cyclic_left _ (toIxxMod_cyclic_left _ h₂₃₄.1)
      rw [(AddCommGroup.not_modEq_iff_toIcoMod_eq_toIocMod hp).1 h] at h₂₃₄'
      exact toIxxMod_cyclic_left _ (h₁₂₃'.trans h₂₃₄')
    by_contra h
    rw [(AddCommGroup.modEq_iff_toIcoMod_eq_left hp).1 h] at h₁₂₃
    exact h₁₂₃.2 (left_lt_toIocMod _ _ _).le
  · rw [not_le] at h₁₂₃ h₂₃₄ ⊢
    exact (h₁₂₃.2.trans_le (toIcoMod_le_toIocMod _ x₃ x₂)).trans h₂₃₄.2


theorem toIcoMod_sub_ofNat_mul' (a b : R) (m : ℕ) [m.AtLeastTwo] :
    toIcoMod hp (a - ofNat(m) * p) b = toIcoMod hp a b - ofNat(m) * p := toIcoMod_sub_natCast_mul' hp a b m

