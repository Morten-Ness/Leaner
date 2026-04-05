import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem modEq_iff_zsmul : a ≡ b [PMOD p] ↔ ∃ m : ℤ, m • p = b - a := by
  rw [AddCommGroup.modEq_iff_nsmul]
  constructor
  · rintro ⟨m, n, h⟩
    use m - n
    rw [sub_zsmul, ← sub_eq_add_neg, sub_eq_sub_iff_add_eq_add, add_comm b]
    exact mod_cast h
  · rintro ⟨m, h⟩
    use m.toNat, (-m).toNat
    rwa [add_comm _ b, ← sub_eq_sub_iff_add_eq_add, ← natCast_zsmul, ← natCast_zsmul,
      sub_eq_add_neg, ← sub_zsmul, m.toNat_sub_toNat_neg]

