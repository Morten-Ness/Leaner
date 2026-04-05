import Mathlib

variable {α : Type*}

variable {ι : Type*} {α : ι → Type*} [∀ i, AddGroup (α i)] [∀ i, Lattice (α i)]

theorem abs_def (f : ∀ i, α i) : |f| = fun i ↦ |f i| := rfl

