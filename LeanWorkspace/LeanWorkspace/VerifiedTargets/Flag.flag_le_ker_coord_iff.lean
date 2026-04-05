import Mathlib

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

theorem flag_le_ker_coord_iff [Nontrivial R] (b : Module.Basis (Fin n) R M) {k : Fin (n + 1)} {l : Fin n} :
    b.flag k ≤ LinearMap.ker (b.coord l) ↔ k ≤ l.castSucc := by
  simp [Module.Basis.flag_le_iff, Finsupp.single_apply_eq_zero, imp_false, imp_not_comm]

