import Mathlib

variable {R ι : Type*} [Preorder ι] {G : ι → Type*}

variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}

variable [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)] [DirectedSystem G (f · · ·)]

variable [IsDirectedOrder ι]

variable [Nonempty ι]

variable [∀ i, AddGroupWithOne (G i)] [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)]

theorem intCast_def [∀ i j h, OneHomClass (T h) (G i) (G j)] (n : ℤ) (i) :
    (n : DirectLimit G f) = ⟦⟨i, n⟩⟧ := map₀_def _ _ (fun _ _ _ ↦ map_intCast' _ (map_one _) _) _

