import Mathlib

variable {R M : Type*}

variable [Ring R] [AddCommGroup M] [Module R M]

variable {I : Ideal R} {r : R}

theorem IsTorsionBySet.isSemisimpleModule_iff [I.IsTwoSided]
    (hM : Module.IsTorsionBySet R M I) : let _ := hM.module
    IsSemisimpleModule (R ⧸ I) M ↔ IsSemisimpleModule R M :=
  let _ := hM.module
  (hM.semilinearMap.isSemisimpleModule_iff_of_bijective Function.bijective_id).symm

