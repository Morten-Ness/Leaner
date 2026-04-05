import Mathlib

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}
  (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)

theorem homology_exact₃ : (ShortComplex.mk _ _ (CategoryTheory.ShortComplex.ShortExact.comp_δ hS i j hij)).Exact := (HomologicalComplex.HomologySequence.snakeInput hS i j hij).L₁'_exact

