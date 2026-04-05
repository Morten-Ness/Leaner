import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable (n : ℕ)

theorem image_support_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} :
    ((MvPolynomial.finSuccEquiv R n f).coeff i).support.image (Finsupp.cons i) = {m ∈ f.support | m 0 = i} := by
  ext m
  rw [Finset.mem_filter, Finset.mem_image, mem_support_iff]
  conv_lhs =>
    congr
    ext
    rw [mem_support_iff, MvPolynomial.finSuccEquiv_coeff_coeff, Ne]
  constructor
  · grind [cons_zero]
  · intro h
    use tail m
    rw [← h.2, cons_tail]
    simp [h.1]

