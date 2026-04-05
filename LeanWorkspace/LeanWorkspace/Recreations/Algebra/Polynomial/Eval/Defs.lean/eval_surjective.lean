import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable {x : R}

theorem eval_surjective (x : R) : Function.Surjective <| Polynomial.eval x := fun y => ⟨Polynomial.C y, Polynomial.eval_C⟩

