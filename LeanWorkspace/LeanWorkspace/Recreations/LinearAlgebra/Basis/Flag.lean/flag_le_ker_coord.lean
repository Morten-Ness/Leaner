import Mathlib

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

theorem flag_le_ker_coord (b : Module.Basis (Fin n) R M) {k : Fin (n + 1)} {l : Fin n}
    (h : k ≤ l.castSucc) : b.flag k ≤ LinearMap.ker (b.coord l) := by
  nontriviality R
  exact Module.Basis.flag_le_ker_coord_iff b.2 h

