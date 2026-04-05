import Mathlib

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}
  (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)

theorem isIso_δ (hi : IsZero (S.X₂.homology i)) (hj : IsZero (S.X₂.homology j)) :
    IsIso (hS.δ i j hij) := (HomologicalComplex.HomologySequence.snakeInput _ _ _ _).isIso_δ hi hj

