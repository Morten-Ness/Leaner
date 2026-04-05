import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [Monoid M] [Monoid N]

theorem induction_on {p : R[M] → Prop} (x : R[M])
    (hM : ∀ m, p (MonoidAlgebra.of R M m)) (hadd : ∀ x y : R[M], p x → p y → p (x + y))
    (hsmul : ∀ (r : R) (x), p x → p (r • x)) : p x := Finsupp.induction_linear x (by simpa using hsmul 0 (MonoidAlgebra.of R M 1) (hM 1))
    (fun x y hf hg => hadd x y hf hg) fun m r ↦ by simpa using hsmul r (MonoidAlgebra.of R M m) (hM m)

