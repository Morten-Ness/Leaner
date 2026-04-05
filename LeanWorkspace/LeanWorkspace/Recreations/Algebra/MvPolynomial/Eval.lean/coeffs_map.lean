import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem coeffs_map (f : R →+* S₁) (p : MvPolynomial σ R) [DecidableEq S₁] :
    (MvPolynomial.map f p).coeffs ⊆ p.coeffs.image f := by
  classical
  induction p using induction_on'' with
  | C a => aesop (add simp coeffs_C)
  | mul_X p n ih => simpa
  | monomial_add a s p ha hs hp ih =>
    rw [coeffs_add (disjoint_support_monomial ha hs), map_add, coeffs_add]
    · rw [Finset.image_union, Finset.union_subset_iff]
      exact ⟨ih.trans (by simp), hp.trans (by simp)⟩
    · exact Finset.disjoint_of_subset_left (MvPolynomial.support_map_subset _ _) <|
        Finset.disjoint_of_subset_right (MvPolynomial.support_map_subset _ _) <|
          disjoint_support_monomial ha hs

