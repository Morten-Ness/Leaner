import Mathlib

open scoped Matrix

variable {R L M n ι ι' ιM : Type*}

variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

variable (φ : L →ₗ[R] Module.End R M)

variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

variable [Module.Free R M] [Module.Finite R M] (b : Basis ι R L)

theorem polyCharpoly_coeff_eq_zero_of_basis (b : Module.Basis ι R L) (b' : Module.Basis ι' R L) (k : ℕ)
    (H : (LinearMap.polyCharpoly φ b).coeff k = 0) :
    (LinearMap.polyCharpoly φ b').coeff k = 0 := by
  rw [LinearMap.polyCharpoly, LinearMap.polyCharpolyAux, Polynomial.coeff_map] at H ⊢
  set B := (Module.Free.chooseBasis R M).end
  set g := LinearMap.toMvPolynomial b' b LinearMap.id
  apply_fun (MvPolynomial.bind₁ g) at H
  have : LinearMap.toMvPolynomial b' B φ = fun i ↦ (MvPolynomial.bind₁ g) (LinearMap.toMvPolynomial b B φ i) :=
    funext <| LinearMap.toMvPolynomial_comp b' b B φ LinearMap.id
  rwa [map_zero, RingHom.coe_coe, MvPolynomial.bind₁_bind₁, ← this] at H

