import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem eval₂_eq_eval_map (g : σ → S₁) (p : MvPolynomial σ R) : p.eval₂ f g = MvPolynomial.eval g (MvPolynomial.map f p) := by
  unfold MvPolynomial.map MvPolynomial.eval; simp only [MvPolynomial.coe_eval₂Hom]
  have h := MvPolynomial.eval₂_comp_left (MvPolynomial.eval₂Hom (RingHom.id S₁) g) (C.comp f) X p
  dsimp only [MvPolynomial.coe_eval₂Hom] at h
  rw [h]
  congr
  · ext1 a
    simp
  · ext1 n
    simp only [comp_apply, MvPolynomial.eval₂_X]

