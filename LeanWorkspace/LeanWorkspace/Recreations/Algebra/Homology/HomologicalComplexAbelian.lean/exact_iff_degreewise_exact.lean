import Mathlib

variable {C ι : Type*} {c : ComplexShape ι} [Category* C]

variable [Abelian C]

variable (S : ShortComplex (HomologicalComplex C c))

theorem exact_iff_degreewise_exact :
    S.Exact ↔ ∀ (i : ι), (S.map (eval C c i)).Exact := by
  constructor
  · intro hS i
    exact hS.map (eval C c i)
  · exact HomologicalComplex.exact_of_degreewise_exact S

