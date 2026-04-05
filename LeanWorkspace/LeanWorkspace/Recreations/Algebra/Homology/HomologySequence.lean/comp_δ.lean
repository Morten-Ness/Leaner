import Mathlib

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}
  (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)

theorem comp_δ : HomologicalComplex.homologyMap S.g i ≫ hS.δ i j hij = 0 := (HomologicalComplex.HomologySequence.snakeInput hS i j hij).L₀_g_δ

