import Mathlib

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {n : ℕ}

theorem flag_wcovBy (b : Module.Basis (Fin n) K V) (i : Fin n) :
    b.flag i.castSucc ⩿ b.flag i.succ := (Module.Basis.flag_covBy b i).wcovBy

