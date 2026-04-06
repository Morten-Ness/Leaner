FAIL
import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable {I J : Submodule R A} {N P : Submodule R M}

theorem smul_induction_on' {x : M} (hx : x ∈ I • N) {p : ∀ x, x ∈ I • N → Prop}
    (smul : ∀ (r : A) (hr : r ∈ I) (n : M) (hn : n ∈ N), p (r • n) (Submodule.smul_mem_smul hr hn))
    (add : ∀ x hx y hy, p x hx → p y hy → p (x + y) (add_mem ‹_› ‹_›)) : p x hx := by
  classical
  let q : M → Prop := fun y => ∀ hy : y ∈ I • N, p y hy
  have hq : q x := by
    refine Submodule.smul_induction_on (p := q) hx ?_ ?_
    · intro r hr n hn hy
      simpa using smul r hr n hn
    · intro y hy z hz hyq hzq hyz
      exact add y hy z hz (hyq hy) (hzq hz)
  exact hq hx
