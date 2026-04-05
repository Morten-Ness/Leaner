import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

variable [Balanced C]

theorem map_of_mono_of_preservesKernel (hS : S.Exact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [(S.map F).HasHomology] (_ : Mono S.f)
    (_ : PreservesLimit (parallelPair S.g 0) F) :
    (S.map F).Exact := CategoryTheory.ShortComplex.exact_of_f_is_kernel _ (KernelFork.mapIsLimit _ hS.fIsKernel F)

