import Mathlib

section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

theorem flag_le_ker_coord_iff [Nontrivial R] (b : Module.Basis (Fin n) R M) {k : Fin (n + 1)} {l : Fin n} :
    b.flag k ≤ LinearMap.ker (b.coord l) ↔ k ≤ l.castSucc := by
  simp [Module.Basis.flag_le_iff, Finsupp.single_apply_eq_zero, imp_false, imp_not_comm]

end

section

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {n : ℕ}

theorem flag_wcovBy (b : Module.Basis (Fin n) K V) (i : Fin n) :
    b.flag i.castSucc ⩿ b.flag i.succ := (Module.Basis.flag_covBy b i).wcovBy

end
