import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable (n : ℕ)

set_option backward.isDefEq.respectTransparency false in
theorem support_finSuccEquiv (f : MvPolynomial (Fin (n + 1)) R) :
    (MvPolynomial.finSuccEquiv R n f).support = Finset.image (fun m : Fin (n + 1) →₀ ℕ => m 0) f.support := by
  ext i
  rw [Polynomial.mem_support_iff, Finset.mem_image, Finsupp.ne_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨cons i m, ?_, cons_zero _ _⟩
    rw [← MvPolynomial.mem_support_coeff_finSuccEquiv]
    simpa using hm
  · rintro ⟨m, h, rfl⟩
    refine ⟨tail m, ?_⟩
    rwa [← coeff, zero_apply, ← mem_support_iff, MvPolynomial.mem_support_coeff_finSuccEquiv, cons_tail]

