import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem map_injective_iff : Function.Injective (MvPolynomial.map (σ := σ) f) ↔ Function.Injective f :=
  ⟨fun h r r' eq ↦ by simpa using h (a₁ := C r) (a₂ := C r') (by simpa), MvPolynomial.map_injective f⟩

