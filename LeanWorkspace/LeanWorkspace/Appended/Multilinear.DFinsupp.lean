import Mathlib

section

variable {ι : Type uι} {κ : ι → Type uκ}

variable {S : Type uS} {R : Type uR}

variable {M : ∀ i, κ i → Type uM} {N : (Π i, κ i) → Type uN}

variable [DecidableEq ι] [Fintype ι] [Semiring R]

variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]

variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

theorem dfinsuppFamily_compLinearMap_lsingle [∀ i, DecidableEq (κ i)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) (p : ∀ i, κ i) :
    (MultilinearMap.dfinsuppFamily f).compLinearMap (fun i => DFinsupp.lsingle (p i))
      = (DFinsupp.lsingle p).compMultilinearMap (f p) := MultilinearMap.ext <| MultilinearMap.dfinsuppFamily_single f p

end

section

variable {ι : Type uι} {κ : ι → Type uκ}

variable {S : Type uS} {R : Type uR}

variable {M : ∀ i, κ i → Type uM} {N : (Π i, κ i) → Type uN}

variable [DecidableEq ι] [Fintype ι] [Semiring R]

variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]

variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

theorem dfinsuppFamily_single [∀ i, DecidableEq (κ i)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p))
    (p : ∀ i, κ i) (m : ∀ i, M i (p i)) :
    MultilinearMap.dfinsuppFamily f (fun i => .single (p i) (m i)) = DFinsupp.single p (f p m) := by
  ext q
  obtain rfl | hpq := eq_or_ne q p
  · simp
  · rw [DFinsupp.single_eq_of_ne hpq]
    rw [Function.ne_iff] at hpq
    obtain ⟨i, hpqi⟩ := hpq
    apply (f q).map_coord_zero i
    simp_rw [DFinsupp.single_eq_of_ne hpqi]

end

section

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

end

section

variable {ι : Type uι} {κ : ι → Type uκ}

variable {S : Type uS} {R : Type uR}

variable {M : ∀ i, κ i → Type uM} {N : (Π i, κ i) → Type uN}

variable [DecidableEq ι] [Fintype ι] [Semiring R]

variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]

variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

theorem dfinsuppFamily_single_left_apply [∀ i, DecidableEq (κ i)]
    (p : Π i, κ i) (f : MultilinearMap R (fun i ↦ M i (p i)) (N p)) (x : Π i, Π₀ j, M i j) :
    MultilinearMap.dfinsuppFamily (Pi.single p f) x = DFinsupp.single p (f fun i => x _ (p i)) := by
  ext p'
  obtain rfl | hp := eq_or_ne p p'
  · simp
  · simp [hp]

end

section

variable {ι : Type uι} {κ : ι → Type uκ}

variable {S : Type uS} {R : Type uR}

variable {ι' : Type*} [DecidableEq ι] [Fintype ι] [CommSemiring R]
  [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

theorem freeDFinsuppEquiv_apply [DecidableEq ι'] [Fintype ι']
    (f : Π₀ (_ : (Π i, κ i) × ι'), R) (x : Π i, Π₀ _ : κ i, R) :
    MultilinearMap.freeDFinsuppEquiv f x = ∑ p, f p • .single p.2 ((∏ i, (x i) (p.1 i))) := by
  apply DFinsupp.induction f
  · simp
  · rintro p r f - - hfx
    simp [Finset.sum_add_distrib, add_smul, hfx]

end

section

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

end

section

variable {ι : Type uι} {κ : ι → Type uκ}

variable {S : Type uS} {R : Type uR}

variable {M : ∀ i, κ i → Type uM} {N : (Π i, κ i) → Type uN}

variable [DecidableEq ι] [Fintype ι] [CommSemiring R]

variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]

variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

variable {N : Type*} [AddCommMonoid N] [Module R N] [(i : ι) → DecidableEq (κ i)]

theorem fromDFinsuppEquiv_apply
    [Π i (j : κ i) (x : M i j), Decidable (x ≠ 0)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) N)
    (x : Π i, Π₀ (j : κ i), M i j) :
    MultilinearMap.fromDFinsuppEquiv κ R f x =
      ∑ p ∈ Fintype.piFinset (fun i ↦ (x i).support), f p (fun i ↦ x i (p i)) := by
  classical
  refine (DFinsupp.sumAddHom_apply _ _).trans ?_
  refine Finset.sum_subset (MultilinearMap.support_dfinsuppFamily_subset _ _) ?_
  simp

end

section

variable {ι : Type uι} {κ : ι → Type uκ}

variable {S : Type uS} {R : Type uR}

variable {M : ∀ i, κ i → Type uM} {N : (Π i, κ i) → Type uN}

variable [DecidableEq ι] [Fintype ι] [CommSemiring R]

variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]

variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

variable {N : Type*} [AddCommMonoid N] [Module R N] [(i : ι) → DecidableEq (κ i)]

theorem fromDFinsuppEquiv_single
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) N)
    (p : Π i, κ i) (x : Π i, M i (p i)) :
    MultilinearMap.fromDFinsuppEquiv κ R f (fun i => DFinsupp.single (p i) (x i)) = f p x := by
  simp [MultilinearMap.fromDFinsuppEquiv]

end

section

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

end
