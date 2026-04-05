import Mathlib

variable {σ R : Type u} [CommSemiring R]

theorem cardinalMk_le_max : #(MvPolynomial σ R) ≤ #R ⊔ #σ ⊔ ℵ₀ := MvPolynomial.cardinalMk_le_max_lift.trans <| by rw [lift_id, lift_id]

