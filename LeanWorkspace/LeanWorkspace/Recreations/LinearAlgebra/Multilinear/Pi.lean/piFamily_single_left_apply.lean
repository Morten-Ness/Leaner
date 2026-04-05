import Mathlib

variable {ι : Type uι} {κ : ι → Type uκ}

variable {S : Type uS} {R : Type uR}

variable {M : ∀ i, κ i → Type uM} {N : (Π i, κ i) → Type uN}

variable [Semiring R]

variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]

variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

theorem piFamily_single_left_apply [Fintype ι] [∀ i, DecidableEq (κ i)]
    (p : Π i, κ i) (f : MultilinearMap R (fun i ↦ M i (p i)) (N p)) (x : Π i j, M i j) :
    MultilinearMap.piFamily (Pi.single p f) x = Pi.single p (f fun i => x i (p i)) := by
  ext p'
  obtain rfl | hp := eq_or_ne p p'
  · simp
  · simp [hp]

