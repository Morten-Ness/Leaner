FAIL
import Mathlib

universe uR uS uA uB

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem ext_of_eq_adjoin {S : Subalgebra R A} {s : Set A} (hS : S = Algebra.adjoin R s)
    ⦃φ₁ φ₂ : S →ₐ[R] B⦄
    (h : ∀ x hx, φ₁ ⟨x, hS.ge (Algebra.subset_adjoin hx)⟩ = φ₂ ⟨x, hS.ge (Algebra.subset_adjoin hx)⟩) :
    φ₁ = φ₂ := by
  subst hS
  exact Algebra.adjoin_eq_iSup_of_subset_eq_range ?_ |> by
    intro x
    exact h x
