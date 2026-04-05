import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem neg_modEq_neg : -a ≡ -b [PMOD p] ↔ a ≡ b [PMOD p] := AddCommGroup.modEq_comm.trans <| by simp [AddCommGroup.modEq_iff_zsmul, neg_add_eq_sub]

alias ⟨AddCommGroup.ModEq.of_neg, AddCommGroup.ModEq.neg⟩ := neg_modEq_neg

