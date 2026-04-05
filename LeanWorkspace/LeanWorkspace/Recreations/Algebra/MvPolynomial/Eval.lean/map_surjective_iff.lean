import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem map_surjective_iff : Function.Surjective (MvPolynomial.map (σ := σ) f) ↔ Function.Surjective f :=
  ⟨fun h s ↦ let ⟨p, h⟩ := h (C s); ⟨p.coeff 0, by simpa [MvPolynomial.coeff_map] using congr(coeff 0 $h)⟩,
    MvPolynomial.map_surjective f⟩

