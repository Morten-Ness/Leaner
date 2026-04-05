import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')

theorem not_boundaryLE_prev [e.IsRelIff] {i j : ι} (hi : c.Rel i j) :
    ¬ e.BoundaryLE i := by
  dsimp [ComplexShape.Embedding.BoundaryLE]
  simp only [not_and, not_forall, not_not]
  intro
  exact ⟨j, by simpa only [e.rel_iff] using hi⟩

