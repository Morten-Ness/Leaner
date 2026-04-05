import Mathlib

variable (C : Type*) [Category* C] {ι : Type*} (c : ComplexShape ι) [HasZeroMorphisms C]
  [CategoryWithHomology C]

theorem HomologicalComplex.homologyFunctor_inverts_quasiIso (i : ι) :
    (quasiIso C c).IsInvertedBy (homologyFunctor C c i) := fun _ _ _ hf => by
  rw [mem_quasiIso_iff] at hf
  dsimp
  infer_instance

