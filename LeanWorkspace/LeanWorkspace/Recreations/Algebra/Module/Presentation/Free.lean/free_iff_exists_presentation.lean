import Mathlib

variable {A : Type u} [Ring A] (relations : Relations.{w₀, w₁} A)
  (M : Type v) [AddCommGroup M] [Module A M]

theorem free_iff_exists_presentation :
    Free A M ↔ ∃ (p : Presentation.{v, w₁} A M), IsEmpty p.R := by
  constructor
  · rw [free_def.{_, _, v}]
    rintro ⟨G, ⟨⟨e⟩⟩⟩
    exact ⟨(Module.presentationFinsupp A G).ofLinearEquiv e.symm, by dsimp; infer_instance⟩
  · rintro ⟨p, h⟩
    exact p.toIsPresentation.free

