import Mathlib

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}
  (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)

theorem δ_comp : hS.δ i j hij ≫ HomologicalComplex.homologyMap S.f j = 0 := (HomologicalComplex.HomologySequence.snakeInput hS i j hij).δ_L₃_f

