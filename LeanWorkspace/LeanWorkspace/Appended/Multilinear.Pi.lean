import Mathlib

section

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

end

section

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

end

section

variable {ι : Type uι} {κ : ι → Type uκ}

variable {S : Type uS} {R : Type uR}

variable {M : ∀ i, κ i → Type uM} {N : (Π i, κ i) → Type uN}

variable [Semiring R]

variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]

variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

theorem piFamily_single_left [Fintype ι] [∀ i, DecidableEq (κ i)]
    (p : Π i, κ i) (f : MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    MultilinearMap.piFamily (Pi.single p f) =
      (LinearMap.single R _ p).compMultilinearMap (f.compLinearMap fun i => .proj (p i)) := ext <| MultilinearMap.piFamily_single_left_apply _ _

end

section

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

end
