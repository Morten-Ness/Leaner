import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_transpose (A : Matrix n n α) : (Matrix.adjugate A)ᵀ = Matrix.adjugate Aᵀ := by
  ext i j
  rw [transpose_apply, Matrix.adjugate_apply, Matrix.adjugate_apply, updateRow_transpose, det_transpose]
  rw [det_apply', det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  by_cases h : i = σ j
  · -- Everything except `(i, j)` (= `(σ j, j)`) is given by A, and the rest is a single `1`.
    congr
    ext j'
    subst h
    have : σ j' = σ j ↔ j' = j := σ.injective.eq_iff
    rw [updateRow_apply, updateCol_apply]
    simp_rw [this]
    rw [← dite_eq_ite, ← dite_eq_ite]
    congr 1 with rfl
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · -- Otherwise, we need to show that there is a `0` somewhere in the product.
    have : (∏ j' : n, updateCol A j (Pi.single i 1) (σ j') j') = 0 := by
      apply prod_eq_zero (mem_univ j)
      rw [updateCol_self, Pi.single_eq_of_ne' h]
    rw [this]
    apply prod_eq_zero (mem_univ (σ⁻¹ i))
    simp only [Perm.coe_inv, apply_symm_apply, updateRow_self]
    apply Pi.single_eq_of_ne
    intro h'
    exact h ((symm_apply_eq σ).mp h')

