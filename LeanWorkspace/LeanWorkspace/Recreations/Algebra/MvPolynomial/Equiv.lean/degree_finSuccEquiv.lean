import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable (n : ℕ)

theorem degree_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} (h : f ≠ 0) :
    (MvPolynomial.finSuccEquiv R n f).degree = degreeOf 0 f := by
  -- TODO: these should be lemmas
  have h₀ : ∀ {α β : Type _} (f : α → β), (fun x => x) ∘ f = f := fun f => rfl
  have h₁ : ∀ {α β : Type _} (f : α → β), f ∘ (fun x => x) = f := fun f => rfl
  have h' : ((MvPolynomial.finSuccEquiv R n f).support.sup fun x => x) = degreeOf 0 f := by
    rw [degreeOf_eq_sup, MvPolynomial.support_finSuccEquiv, Finset.sup_image, h₀]
  rw [Polynomial.degree, ← h', Nat.cast_withBot,
    Finset.coe_sup_of_nonempty (MvPolynomial.nonempty_support_finSuccEquiv h), Finset.max_eq_sup_coe, h₁]

