import Mathlib

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {n : ℕ}

theorem flag_covBy (b : Module.Basis (Fin n) K V) (i : Fin n) :
    b.flag i.castSucc ⋖ b.flag i.succ := by
  rw [Module.Basis.flag_succ]
  apply covBy_span_singleton_sup
  simp

