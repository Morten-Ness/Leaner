import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable (n : ℕ)

theorem totalDegree_coeff_finSuccEquiv_add_le (f : MvPolynomial (Fin (n + 1)) R) (i : ℕ)
    (hi : (MvPolynomial.finSuccEquiv R n f).coeff i ≠ 0) :
    totalDegree ((MvPolynomial.finSuccEquiv R n f).coeff i) + i ≤ totalDegree f := by
  have hf'_sup : ((MvPolynomial.finSuccEquiv R n f).coeff i).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, ne_eq, support_eq_empty]
    exact hi
  -- Let σ be a monomial index of ((MvPolynomial.finSuccEquiv R n p).coeff i) of maximal total degree
  have ⟨σ, hσ1, hσ2⟩ := Finset.exists_mem_eq_sup (support _) hf'_sup
                          (fun s => Finsupp.sum s fun _ e => e)
  -- Then cons i σ is a monomial index of p with total degree equal to the desired bound
  let σ' : Fin (n + 1) →₀ ℕ := cons i σ
  convert le_totalDegree (s := σ') _
  · rw [totalDegree, hσ2, sum_cons, add_comm]
  · rw [← MvPolynomial.mem_support_coeff_finSuccEquiv]
    exact hσ1

