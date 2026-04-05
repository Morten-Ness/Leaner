import Mathlib

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {n : ℕ} {b : Basis (Fin n) R M}
  {i j : Fin (n + 1)}

theorem flag_succ (b : Module.Basis (Fin n) R M) (k : Fin n) :
    b.flag k.succ = R ∙ b k ⊔ b.flag k.castSucc := by
  simp only [Module.Basis.flag, Fin.castSucc_lt_castSucc_iff]
  simp [Fin.castSucc_lt_iff_succ_le, le_iff_eq_or_lt, setOf_or, image_insert_eq, span_insert]

