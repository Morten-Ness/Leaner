import Mathlib

variable {ι : Type uι} {κ : ι → Type uκ}

variable {S : Type uS} {R : Type uR}

variable {M : ∀ i, κ i → Type uM} {N : (Π i, κ i) → Type uN}

variable [Semiring R]

variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]

variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

theorem piFamily_single [Fintype ι] [∀ i, DecidableEq (κ i)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p))
    (p : ∀ i, κ i) (m : ∀ i, M i (p i)) :
    MultilinearMap.piFamily f (fun i => Pi.single (p i) (m i)) = Pi.single p (f p m) := by
  ext q
  obtain rfl | hpq := eq_or_ne p q
  · simp
  · rw [Pi.single_eq_of_ne' hpq]
    rw [Function.ne_iff] at hpq
    obtain ⟨i, hpqi⟩ := hpq
    apply (f q).map_coord_zero i
    simp_rw [Pi.single_eq_of_ne' hpqi]

