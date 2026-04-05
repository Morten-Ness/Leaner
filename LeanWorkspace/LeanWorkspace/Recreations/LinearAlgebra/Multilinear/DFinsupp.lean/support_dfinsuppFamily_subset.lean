import Mathlib

variable {ι : Type uι} {κ : ι → Type uκ}

variable {S : Type uS} {R : Type uR}

variable {M : ∀ i, κ i → Type uM} {N : (Π i, κ i) → Type uN}

variable [DecidableEq ι] [Fintype ι] [Semiring R]

variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]

variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

theorem support_dfinsuppFamily_subset
    [∀ i, DecidableEq (κ i)]
    [∀ i j, (x : M i j) → Decidable (x ≠ 0)] [∀ i, (x : N i) → Decidable (x ≠ 0)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p))
    (x : ∀ i, Π₀ j : κ i, M i j) :
    (MultilinearMap.dfinsuppFamily f x).support ⊆ Fintype.piFinset fun i => (x i).support := by
  intro p hp
  simp only [DFinsupp.mem_support_toFun, dfinsuppFamily_apply_toFun, ne_eq,
    Fintype.mem_piFinset] at hp ⊢
  intro i
  exact mt ((f p).map_coord_zero (m := fun i => x i _) i) hp

