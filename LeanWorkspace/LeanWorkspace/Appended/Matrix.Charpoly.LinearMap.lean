import Mathlib

section

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

theorem LinearMap.exists_monic_and_aeval_eq_zero [Module.Finite R M] (f : Module.End R M) :
    ∃ p : R[X], p.Monic ∧ Polynomial.aeval f p = 0 := (LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul R f ⊤ (by simp)).imp
    fun _ h => h.imp_right And.right

end

section

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

theorem LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul
    [Module.Finite R M] (f : Module.End R M) (I : Ideal R) (hI : LinearMap.range f ≤ I • ⊤) :
    ∃ p : R[X], p.Monic ∧ (∀ k, p.coeff k ∈ I ^ (p.natDegree - k)) ∧ Polynomial.aeval f p = 0 := by
  classical
    cases subsingleton_or_nontrivial R
    · exact ⟨0, Polynomial.monic_of_subsingleton _, by simp⟩
    obtain ⟨s : Finset M, hs : Submodule.span R (s : Set M) = ⊤⟩ :=
      Module.Finite.fg_top (R := R) (M := M)
    have : Submodule.span R (Set.range ((↑) : { x // x ∈ s } → M)) = ⊤ := by
      rw [Subtype.range_coe_subtype, Finset.setOf_mem, hs]
    obtain ⟨A, rfl, h⟩ :=
      Matrix.isRepresentation.toEnd_exists_mem_ideal R ((↑) : s → M) this f I hI
    refine ⟨A.1.charpoly, A.1.charpoly_monic, ?_, ?_⟩
    · rw [A.1.charpoly_natDegree_eq_dim]
      exact coeff_charpoly_mem_ideal_pow h
    · rw [Polynomial.aeval_algHom_apply,
        ← map_zero (Matrix.isRepresentation.toEnd R ((↑) : s → M) this)]
      congr 1
      ext1
      rw [Polynomial.aeval_subalgebra_coe, Matrix.aeval_self_charpoly, Subalgebra.coe_zero]

end

section

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

variable {R} [DecidableEq ι]

theorem Matrix.Represents.add {A A' : Matrix ι ι R} {f f' : Module.End R M} (h : A.Represents b f)
    (h' : Matrix.Represents b A' f') : (A + A').Represents b (f + f') := by
  delta Matrix.Represents at h h' ⊢; rw [map_add, map_add, h, h']

end

section

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

variable {R} [DecidableEq ι]

theorem Matrix.Represents.algebraMap (r : R) :
    (algebraMap _ (Matrix ι ι R) r).Represents b (algebraMap _ (Module.End R M) r) := by
  simpa only [Algebra.algebraMap_eq_smul_one] using Matrix.Represents.one.smul r

end

section

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

variable {R} [DecidableEq ι]

theorem Matrix.Represents.eq (hb : Submodule.span R (Set.range b) = ⊤)
    {A : Matrix ι ι R} {f f' : Module.End R M} (h : A.Represents b f)
    (h' : A.Represents b f') : f = f' := PiToModule.fromEnd_injective R b hb (h.symm.trans h')

end

section

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

variable {R} [DecidableEq ι]

theorem Matrix.Represents.mul {A A' : Matrix ι ι R} {f f' : Module.End R M} (h : A.Represents b f)
    (h' : Matrix.Represents b A' f') : (A * A').Represents b (f * f') := by
  delta Matrix.Represents PiToModule.fromMatrix
  rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul]
  ext
  dsimp [PiToModule.fromEnd]
  rw [← h'.congr_fun, ← h.congr_fun]
  rfl

end

section

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

variable {R} [DecidableEq ι]

theorem Matrix.Represents.one : (1 : Matrix ι ι R).Represents b 1 := by
  delta Matrix.Represents PiToModule.fromMatrix
  rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_one]
  ext
  rfl

end

section

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

variable {R} [DecidableEq ι]

theorem Matrix.Represents.smul {A : Matrix ι ι R} {f : Module.End R M} (h : A.Represents b f)
    (r : R) : (r • A).Represents b (r • f) := by
  delta Matrix.Represents at h ⊢
  rw [map_smul, map_smul, h]

end

section

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

variable {R} [DecidableEq ι]

theorem Matrix.Represents.zero : (0 : Matrix ι ι R).Represents b 0 := by
  delta Matrix.Represents
  rw [map_zero, map_zero]

end

section

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

variable {R} [DecidableEq ι]

variable (hb : Submodule.span R (Set.range b) = ⊤)

theorem Matrix.isRepresentation.toEnd_exists_mem_ideal (f : Module.End R M) (I : Ideal R)
    (hI : LinearMap.range f ≤ I • ⊤) :
    ∃ M, Matrix.isRepresentation.toEnd R b hb M = f ∧ ∀ i j, M.1 i j ∈ I := by
  have : ∀ x, f x ∈ LinearMap.range (Ideal.finsuppTotal ι M I b) := by
    rw [Ideal.range_finsuppTotal, hb]
    exact fun x => hI (LinearMap.mem_range_self f x)
  choose bM' hbM' using this
  let A : Matrix ι ι R := fun i j => bM' (b j) i
  have : A.Represents b f := by
    rw [Matrix.represents_iff']
    dsimp [A]
    intro j
    specialize hbM' (b j)
    rwa [Ideal.finsuppTotal_apply_eq_of_fintype] at hbM'
  exact
    ⟨⟨A, f, this⟩, Matrix.isRepresentation.eq_toEnd_of_represents R b hb ⟨A, f, this⟩ this,
      fun i j => (bM' (b j) i).prop⟩

end

section

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

variable {R} [DecidableEq ι]

variable (hb : Submodule.span R (Set.range b) = ⊤)

theorem Matrix.isRepresentation.toEnd_surjective :
    Function.Surjective (Matrix.isRepresentation.toEnd R b hb) := by
  intro f
  obtain ⟨M, e, -⟩ := Matrix.isRepresentation.toEnd_exists_mem_ideal R b hb f ⊤ (by simp)
  exact ⟨M, e⟩

end

section

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

variable {R} [DecidableEq ι]

theorem Matrix.represents_iff' {A : Matrix ι ι R} {f : Module.End R M} :
    A.Represents b f ↔ ∀ j, ∑ i : ι, A i j • b i = f (b j) := by
  constructor
  · intro h i
    have := LinearMap.congr_fun h (Pi.single i 1)
    rwa [PiToModule.fromEnd_apply_single_one, PiToModule.fromMatrix_apply_single_one] at this
  · intro h
    ext
    simp_rw [LinearMap.comp_apply, LinearMap.coe_single, PiToModule.fromEnd_apply_single_one,
      PiToModule.fromMatrix_apply_single_one]
    apply h

end

section

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

variable {R} [DecidableEq ι]

theorem Matrix.represents_iff {A : Matrix ι ι R} {f : Module.End R M} :
    A.Represents b f ↔
      ∀ x, Fintype.linearCombination R b (A *ᵥ x) = f (Fintype.linearCombination R b x) := ⟨fun e x => e.congr_fun x, fun H => LinearMap.ext fun x => H x⟩

end

section

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

theorem PiToModule.fromEnd_apply_single_one [DecidableEq ι] (f : Module.End R M) (i : ι) :
    PiToModule.fromEnd R b f (Pi.single i 1) = f (b i) := by
  rw [PiToModule.fromEnd_apply, Fintype.linearCombination_apply_single, one_smul]

end

section

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

theorem PiToModule.fromEnd_injective (hb : Submodule.span R (Set.range b) = ⊤) :
    Function.Injective (PiToModule.fromEnd R b) := by
  intro x y e
  ext m
  obtain ⟨m, rfl⟩ : m ∈ LinearMap.range (Fintype.linearCombination R b) := by
    rw [(Fintype.range_linearCombination R b).trans hb]
    exact Submodule.mem_top
  exact (LinearMap.congr_fun e m :)

end

section

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

theorem PiToModule.fromMatrix_apply_single_one [DecidableEq ι] (A : Matrix ι ι R) (j : ι) :
    PiToModule.fromMatrix R b A (Pi.single j 1) = ∑ i : ι, A i j • b i := by
  rw [PiToModule.fromMatrix_apply, Fintype.linearCombination_apply, Matrix.mulVec_single]
  simp_rw [MulOpposite.op_one, one_smul, col_apply]

end
