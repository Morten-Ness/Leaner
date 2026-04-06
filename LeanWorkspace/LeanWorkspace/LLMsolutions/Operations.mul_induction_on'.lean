FAIL
import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable [IsScalarTower R A A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem mul_induction_on' {C : ∀ r, r ∈ M * N → Prop}
    (mem_mul_mem : ∀ m (hm : m ∈ M) n (hn : n ∈ N), C (m * n) (Submodule.mul_mem_mul hm hn))
    (add : ∀ x hx y hy, C x hx → C y hy → C (x + y) (add_mem hx hy)) {r : A} (hr : r ∈ M * N) :
    C r hr := by
  let P : Submodule R A := { x | ∃ hx : x ∈ M * N, C x hx }
  have hPmul : ∀ m (hm : m ∈ M) n (hn : n ∈ N), m * n ∈ P := by
    intro m hm n hn
    exact ⟨Submodule.mul_mem_mul hm hn, mem_mul_mem m hm n hn⟩
  have hPadd : ∀ x y, x ∈ P → y ∈ P → x + y ∈ P := by
    intro x y hx hy
    rcases hx with ⟨hx', hxC⟩
    rcases hy with ⟨hy', hyC⟩
    exact ⟨add_mem hx' hy', add x hx' y hy' hxC hyC⟩
  have hrP : r ∈ P := by
    exact Submodule.mul_induction_on hr hPmul hPadd
  rcases hrP with ⟨hr', hCr⟩
  exact hCr
