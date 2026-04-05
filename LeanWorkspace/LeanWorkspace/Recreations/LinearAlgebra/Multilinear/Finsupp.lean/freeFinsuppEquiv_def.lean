import Mathlib

variable {ι ι' R : Type*} {κ : ι → Type*}

variable [DecidableEq ι] [Fintype ι] [CommSemiring R] [DecidableEq R]
  [DecidableEq ι'] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

theorem freeFinsuppEquiv_def (f : ((Π i, κ i) × ι') →₀ R) :
    MultilinearMap.freeFinsuppEquiv f =
      LinearEquiv.multilinearMapCongrLeft (fun _ => finsuppLequivDFinsupp R)
      (((finsuppLequivDFinsupp R).multilinearMapCongrRight R).symm <|
      freeDFinsuppEquiv (finsuppLequivDFinsupp R f)) := rfl

