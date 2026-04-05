import Mathlib

variable {R A : Type*} [CommSemiring R]

variable [AddCommMonoid A] [Module R A] [Module (Polynomial R) A]

theorem derivation_ext {D₁ D₂ : Derivation R R[X] A} (h : D₁ X = D₂ X) : D₁ = D₂ := Derivation.ext fun f => Derivation.eqOn_adjoin (Set.eqOn_singleton.2 h) <| by
    simp only [adjoin_X, Algebra.coe_top, Set.mem_univ]

