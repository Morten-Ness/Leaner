import Mathlib

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

variable [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)] (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

variable [DecidableEq ι]

theorem exists_of [Nonempty ι] [IsDirectedOrder ι] (z : Module.DirectLimit G f) :
    ∃ i x, Module.DirectLimit.of R ι G f i x = z := Nonempty.elim (by infer_instance) fun ind : ι ↦
    Quotient.inductionOn' z fun z ↦
      DirectSum.induction_on z ⟨ind, 0, map_zero _⟩ (fun i x ↦ ⟨i, x, rfl⟩)
        fun p q ⟨i, x, ihx⟩ ⟨j, y, ihy⟩ ↦
        let ⟨k, hik, hjk⟩ := exists_ge_ge i j
        ⟨k, f i k hik x + f j k hjk y, by
          rw [map_add, Module.DirectLimit.of_f, Module.DirectLimit.of_f, ihx, ihy]
          rfl ⟩

