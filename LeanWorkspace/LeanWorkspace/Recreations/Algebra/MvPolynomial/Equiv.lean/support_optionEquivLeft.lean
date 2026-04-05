import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

set_option backward.isDefEq.respectTransparency false in
theorem support_optionEquivLeft (p : MvPolynomial (Option σ) R) :
    (MvPolynomial.optionEquivLeft R σ p).support = Finset.image (fun m => m none) p.support := by
  ext i
  rw [Polynomial.mem_support_iff, Finset.mem_image, Finsupp.ne_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨optionElim i m, ?_, optionElim_apply_none _ _⟩
    rw [← MvPolynomial.mem_support_coeff_optionEquivLeft]
    simpa using hm
  · rintro ⟨m, h, rfl⟩
    refine ⟨some m, ?_⟩
    rwa [← coeff, zero_apply, ← mem_support_iff, MvPolynomial.mem_support_coeff_optionEquivLeft, optionElim_some]

