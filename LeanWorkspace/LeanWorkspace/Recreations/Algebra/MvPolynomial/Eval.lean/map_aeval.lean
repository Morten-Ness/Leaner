import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable [Algebra R S₁] [CommSemiring S₂]

variable (f : σ → S₁)

theorem map_aeval {B : Type*} [CommSemiring B] (g : σ → S₁) (φ : S₁ →+* B) (p : MvPolynomial σ R) :
    φ (MvPolynomial.aeval g p) = MvPolynomial.eval₂Hom (φ.comp (algebraMap R S₁)) (fun i => φ (g i)) p := by
  rw [← MvPolynomial.comp_eval₂Hom]
  rfl

