import Mathlib

variable {ι : Type uι} {κ : ι → Type uκ}

variable {S : Type uS} {R : Type uR}

variable {M : ∀ i, κ i → Type uM} {N : (Π i, κ i) → Type uN}

variable [Semiring R]

variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]

variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

theorem piFamily_compLinearMap_lsingle [Fintype ι] [∀ i, DecidableEq (κ i)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) (p : ∀ i, κ i) :
    (MultilinearMap.piFamily f).compLinearMap (fun i => LinearMap.single _ _ (p i))
      = (LinearMap.single _ _ p).compMultilinearMap (f p) := MultilinearMap.ext <| MultilinearMap.piFamily_single f p

