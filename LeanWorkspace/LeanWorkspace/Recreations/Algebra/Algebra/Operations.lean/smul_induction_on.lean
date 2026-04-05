import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable {I J : Submodule R A} {N P : Submodule R M}

theorem smul_induction_on {p : M → Prop} {x} (H : x ∈ I • N) (smul : ∀ r ∈ I, ∀ n ∈ N, p (r • n))
    (add : ∀ x y, p x → p y → p (x + y)) : p x := AddSubmonoid.smul_induction_on H smul add

