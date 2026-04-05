import Mathlib

open scoped Polynomial

variable (R : Type*) {M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

theorem induction_linear {motive : PolynomialModule R M → Prop} (f : PolynomialModule R M)
    (zero : motive 0) (add : ∀ f g, motive f → motive g → motive (f + g))
    (PolynomialModule.single : ∀ a b, motive (PolynomialModule.single R a b)) : motive f := Finsupp.induction_linear f zero add PolynomialModule.single

noncomputable instance polynomialModule : Module R[X] (PolynomialModule R M) :=
  inferInstanceAs (Module R[X] (Module.AEval' (Finsupp.lmapDomain M R Nat.succ)))

