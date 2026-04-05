import Mathlib

variable {ι : Type uι} {κ : ι → Type uκ}

variable {S : Type uS} {R : Type uR}

variable {M : ∀ i, κ i → Type uM} {N : (Π i, κ i) → Type uN}

variable [Semiring R]

variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]

variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

theorem piFamily_smul
    [Monoid S] [∀ p, DistribMulAction S (N p)] [∀ p, SMulCommClass R S (N p)]
    (s : S) (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    MultilinearMap.piFamily (s • f) = s • MultilinearMap.piFamily f := by
  ext; simp

