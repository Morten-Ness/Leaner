import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R]

theorem induction_on [AddMonoid M] {p : R[M] → Prop} (x : R[M])
    (hM : ∀ m, p (AddMonoidAlgebra.of R M <| .ofAdd m)) (hadd : ∀ x y : R[M], p x → p y → p (x + y))
    (hsmul : ∀ (r : R) (x), p x → p (r • x)) : p x := Finsupp.induction_linear x (by simpa using hsmul 0 (AddMonoidAlgebra.of R M 1) (hM 0))
    (fun x y hf hg ↦ hadd x y hf hg) fun m r ↦ by simpa using hsmul r (AddMonoidAlgebra.of R M m) (hM m)

