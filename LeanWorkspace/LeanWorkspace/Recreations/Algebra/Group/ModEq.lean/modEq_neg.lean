import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem modEq_neg : a ≡ b [PMOD -p] ↔ a ≡ b [PMOD p] := AddCommGroup.modEq_comm.trans <| by simp [AddCommGroup.modEq_iff_zsmul, neg_eq_iff_eq_neg]

alias ⟨AddCommGroup.ModEq.of_neg', AddCommGroup.ModEq.neg'⟩ := modEq_neg

