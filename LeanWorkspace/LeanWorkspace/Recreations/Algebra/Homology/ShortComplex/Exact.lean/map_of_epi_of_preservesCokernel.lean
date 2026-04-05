import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

variable [Balanced C]

theorem map_of_epi_of_preservesCokernel (hS : S.Exact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [(S.map F).HasHomology] (_ : Epi S.g)
    (_ : PreservesColimit (parallelPair S.f 0) F) :
    (S.map F).Exact := CategoryTheory.ShortComplex.exact_of_g_is_cokernel _ (CokernelCofork.mapIsColimit _ hS.gIsCokernel F)

