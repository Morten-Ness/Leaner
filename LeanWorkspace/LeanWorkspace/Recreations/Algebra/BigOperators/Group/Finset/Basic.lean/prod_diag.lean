import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_diag (s : Finset ι) (f : ι × ι → M) :
    ∏ i ∈ s.diag, f i = ∏ i ∈ s, f (i, i) := by
  simp [diag]

