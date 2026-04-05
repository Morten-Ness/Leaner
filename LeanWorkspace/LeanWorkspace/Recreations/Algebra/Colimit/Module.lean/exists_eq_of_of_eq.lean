import Mathlib

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

variable [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)] (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

variable [DecidableEq ι]

variable {G f} [DirectedSystem G (f · · ·)] [IsDirectedOrder ι]

theorem exists_eq_of_of_eq {i x y} (h : Module.DirectLimit.of R ι G f i x = Module.DirectLimit.of R ι G f i y) :
    ∃ j hij, f i j hij x = f i j hij y := by
  have := Nonempty.intro i
  apply_fun Module.DirectLimit.linearEquiv _ _ at h
  simp_rw [Module.DirectLimit.linearEquiv_of] at h
  have ⟨j, h⟩ := Quotient.exact h
  exact ⟨j, h.1, h.2.2⟩

