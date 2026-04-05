import Mathlib

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}
  (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)

theorem mono_δ (hi : IsZero (S.X₂.homology i)) : Mono (hS.δ i j hij) := (HomologicalComplex.HomologySequence.snakeInput _ _ _ _).mono_δ hi

