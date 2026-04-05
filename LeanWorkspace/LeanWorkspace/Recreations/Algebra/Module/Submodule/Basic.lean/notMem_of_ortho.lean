import Mathlib

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

variable [Ring R] [IsDomain R]

variable [AddCommGroup M] [Module R M] {b : ι → M}

theorem notMem_of_ortho {x : M} {N : Submodule R M}
    (ortho : ∀ (c : R), ∀ y ∈ N, c • x + y = (0 : M) → c = 0) : x ∉ N := by
  intro hx
  simpa using ortho (-1) x hx

