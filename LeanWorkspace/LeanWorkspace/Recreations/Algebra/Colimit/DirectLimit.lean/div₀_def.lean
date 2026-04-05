import Mathlib

variable {R ι : Type*} [Preorder ι] {G : ι → Type*}

variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}

variable [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)] [DirectedSystem G (f · · ·)]

variable [IsDirectedOrder ι]

variable [Nonempty ι]

variable [∀ i, GroupWithZero (G i)] [∀ i j h, MonoidWithZeroHomClass (T h) (G i) (G j)]

theorem div₀_def (i x y) : ⟦⟨i, x⟩⟧ / ⟦⟨i, y⟩⟧ = (⟦⟨i, x / y⟩⟧ : DirectLimit G f) := map₂_def ..

