import Mathlib

variable {ι : Type uι} {κ : ι → Type uκ}

variable {S : Type uS} {R : Type uR}

variable {ι' : Type*} [DecidableEq ι] [Fintype ι] [CommSemiring R]
  [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

theorem freeDFinsuppEquiv_def (f : Π₀ (_ : (Π i, κ i) × ι'), R) :
    MultilinearMap.freeDFinsuppEquiv f =
      MultilinearMap.fromDFinsuppEquiv κ R
      (LinearEquiv.piCongrRight (fun _ => MultilinearMap.piRingEquiv) <|
      DFinsupp.linearEquivFunOnFintype (R := R) <|
      DFinsupp.sigmaCurryLEquiv (R := R) <|
      (DFinsupp.domLCongr (R := R) (Equiv.sigmaEquivProd _ _).symm) f) :=
  rfl

