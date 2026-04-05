import Mathlib

variable {ι : Type uι} {κ : ι → Type uκ}

variable {S : Type uS} {R : Type uR}

variable {M : ∀ i, κ i → Type uM} {N : (Π i, κ i) → Type uN}

variable [DecidableEq ι] [Fintype ι] [CommSemiring R]

variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]

variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

variable {N : Type*} [AddCommMonoid N] [Module R N] [(i : ι) → DecidableEq (κ i)]

theorem fromDFinsuppEquiv_symm_apply (f : MultilinearMap R (fun i ↦ Π₀ j : κ i, M i j) N)
    (p : Π i, κ i) :
    (MultilinearMap.fromDFinsuppEquiv κ R).symm f p = f.compLinearMap (fun i ↦ DFinsupp.lsingle (p i)) := rfl

