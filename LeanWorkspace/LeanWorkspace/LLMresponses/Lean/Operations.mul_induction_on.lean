FAIL
import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable [IsScalarTower R A A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem mul_induction_on {C : A → Prop} {r : A} (hr : r ∈ M * N)
    (hm : ∀ m ∈ M, ∀ n ∈ N, C (m * n)) (ha : ∀ x y, C x → C y → C (x + y)) : C r := by
  classical
  simpa using hr using
    (Submodule.mul_induction_on (p := C) (M := M) (N := N) (r := r) hr hm
      (by
        intro x y hx hy
        exact ha x y hx hy)
      (by
        exact hm 0 M.zero_mem 0 N.zero_mem))
