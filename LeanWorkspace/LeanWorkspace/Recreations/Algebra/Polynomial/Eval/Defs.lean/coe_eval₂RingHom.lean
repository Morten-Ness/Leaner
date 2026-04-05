import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [CommSemiring S] (f : R →+* S) (x : S)

theorem coe_eval₂RingHom (f : R →+* S) (x) : ⇑(Polynomial.eval₂RingHom f x) = eval₂ f x := rfl

