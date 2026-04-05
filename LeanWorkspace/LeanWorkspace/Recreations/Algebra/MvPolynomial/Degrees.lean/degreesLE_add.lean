import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

variable {s t : Multiset σ}

theorem degreesLE_add : MvPolynomial.degreesLE R σ (s + t) = MvPolynomial.degreesLE R σ s * MvPolynomial.degreesLE R σ t := by
  classical
  rw [le_antisymm_iff, Submodule.mul_le]
  refine ⟨fun x hx ↦ x.as_sum ▸ sum_mem fun i hi ↦ ?_,
    fun x hx y hy ↦ MvPolynomial.degrees_mul_le.trans (add_le_add hx hy)⟩
  replace hi : i.toMultiset ≤ s + t := (Finset.le_sup hi).trans hx
  let a := (i.toMultiset - t).toFinsupp
  let b := (i.toMultiset ⊓ t).toFinsupp
  have : a + b = i := Multiset.toFinsupp.symm.injective (by simp [a, b, Multiset.sub_add_inter])
  have ha : a.toMultiset ≤ s := by simpa [a, add_comm (a := t)] using hi
  have hb : b.toMultiset ≤ t := by simp [b, Multiset.inter_le_right]
  rw [show monomial i (x.coeff i) = monomial a (x.coeff i) * monomial b 1 by simp [this]]
  exact Submodule.mul_mem_mul ((MvPolynomial.degrees_monomial _ _).trans ha) ((MvPolynomial.degrees_monomial _ _).trans hb)

