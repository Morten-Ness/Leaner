import Mathlib

variable {R ι : Type*} [Preorder ι] {G : ι → Type*}

variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}

variable [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)] [DirectedSystem G (f · · ·)]

variable [IsDirectedOrder ι]

variable [Nonempty ι]

variable [∀ i, DivisionSemiring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)]

theorem nnratCast_def (q : ℚ≥0) (i) : (q : DirectLimit G f) = ⟦⟨i, q⟩⟧ := map₀_def _ _ (fun _ _ _ ↦ map_nnratCast _ _) _

