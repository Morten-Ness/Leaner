import Mathlib

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {n : ℕ}

theorem flag_wcovBy (b : Module.Basis (Fin n) K V) (i : Fin n) :
    b.flag i.castSucc ⩿ b.flag i.succ := by
  rcases b.flag_covBy i with ⟨hlt, hcov⟩
  exact ⟨hlt.le, fun z hz1 hz2 => hcov hz1 hz2⟩
