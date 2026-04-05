import Mathlib

variable {ι : Type uι} {κ : ι → Type uκ}

variable {S : Type uS} {R : Type uR}

variable {M : ∀ i, κ i → Type uM} {N : (Π i, κ i) → Type uN}

variable [DecidableEq ι] [Fintype ι] [Semiring R]

variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]

variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

theorem dfinsuppFamily_single_left [∀ i, DecidableEq (κ i)]
    (p : Π i, κ i) (f : MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    MultilinearMap.dfinsuppFamily (Pi.single p f) =
      (DFinsupp.lsingle p).compMultilinearMap (f.compLinearMap fun i => DFinsupp.lapply (p i)) := ext <| MultilinearMap.dfinsuppFamily_single_left_apply _ _

