FAIL
import Mathlib

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}

theorem flag_le_ker_coord_iff [Nontrivial R] (b : Module.Basis (Fin n) R M) {k : Fin (n + 1)} {l : Fin n} :
    b.flag k ≤ LinearMap.ker (b.coord l) ↔ k ≤ l.castSucc := by
  classical
  constructor
  · intro h
    by_contra hk
    have hlt : l.castSucc < k := lt_of_not_ge hk
    have hb : b l ∈ b.flag k := by
      rw [Module.Basis.mem_flag]
      exact hlt
    have hk0 : b.coord l (b l) = 0 := by
      exact h hb
    have hk1 : b.coord l (b l) = 1 := by
      simp
    exact one_ne_zero (hk1.trans hk0.symm)
  · intro hk
    rw [LinearMap.ker_le_iff]
    intro x hx
    rw [Submodule.mem_carrier] at hx ⊢
    rw [LinearMap.mem_ker]
    by_contra hxl
    have hbl : b l ∈ Submodule.span R (↑b '' {i : Fin n | ↑i < ↑k}) := by
      apply Submodule.subset_span
      refine ⟨l, ?_, rfl⟩
      change l.castSucc < k
      exact lt_of_not_ge hk
    have hnot : b l ∉ LinearMap.ker (b.coord l) := by
      rw [LinearMap.mem_ker]
      simp
    exact hnot (hx hbl)
