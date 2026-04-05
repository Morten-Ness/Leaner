import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

variable {α β : Type*}

theorem smul_def [SMul A α] {S : Subalgebra R A} (g : S) (m : α) : g • m = (g : A) • m := rfl

