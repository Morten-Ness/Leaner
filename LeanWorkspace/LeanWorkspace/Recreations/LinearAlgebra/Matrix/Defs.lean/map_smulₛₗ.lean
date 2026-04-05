import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem map_smulₛₗ [SMul R α] [SMul S β] (f : α → β) (σ : R → S) (r : R)
    (hf : ∀ a, f (r • a) = σ r • f a)
    (M : Matrix m n α) : (r • M).map f = σ r • M.map f := Matrix.ext fun _ _ => hf _

