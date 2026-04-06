import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable {I J : Submodule R A} {N P : Submodule R M}

theorem smul_induction_on {p : M → Prop} {x} (H : x ∈ I • N) (smul : ∀ r ∈ I, ∀ n ∈ N, p (r • n))
    (add : ∀ x y, p x → p y → p (x + y)) : p x := by
  refine Submodule.smul_induction_on (p := p) (I := I) (N := N) H ?_ ?_
  · intro r hr n hn
    exact smul r hr n hn
  · intro x y hx hy
    exact add x y hx hy
