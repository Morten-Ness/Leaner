import Mathlib

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}
  (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)

theorem epi_δ (hj : IsZero (S.X₂.homology j)) : Epi (hS.δ i j hij) := (HomologicalComplex.HomologySequence.snakeInput _ _ _ _).epi_δ hj

