import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

variable [LinearOrder σ]

theorem leadingCoeff_toLex : p.leadingCoeff toLex = p.coeff (ofLex <| p.supDegree toLex) := by
  rw [leadingCoeff]
  apply congr_arg p.coeff
  apply toLex.injective
  rw [Function.rightInverse_invFun toLex.surjective, toLex_ofLex]

