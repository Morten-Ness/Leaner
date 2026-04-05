import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')

theorem not_boundaryGE_next [e.IsRelIff] {j k : ι} (hk : c.Rel j k) :
    ¬ e.BoundaryGE k := by
  dsimp [ComplexShape.Embedding.BoundaryGE]
  simp only [not_and, not_forall, not_not]
  intro
  exact ⟨j, by simpa only [e.rel_iff] using hk⟩

