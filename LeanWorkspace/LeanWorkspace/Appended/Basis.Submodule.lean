import Mathlib

section

variable {ι ι' R R₂ M M' : Type*}

variable {v : ι → M}

variable [Ring R] [CommRing R₂] [AddCommGroup M]

variable [Module R M] [Module R₂ M]

variable {x y : M}

variable (b : Basis ι R M)

theorem Basis.eq_bot_of_rank_eq_zero [IsDomain R] (b : Basis ι R M) (N : Submodule R M)
    (rank_eq : ∀ {m : ℕ} (v : Fin m → N), LinearIndependent R ((↑) ∘ v : Fin m → M) → m = 0) :
    N = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  contrapose! rank_eq with x_ne
  refine ⟨1, fun _ => ⟨x, hx⟩, ?_, one_ne_zero⟩
  rw [Fintype.linearIndependent_iff]
  rintro g sum_eq i
  simp only [Fin.default_eq_zero, Finset.univ_unique,
    Finset.sum_singleton] at sum_eq
  convert (b.smul_eq_zero.mp sum_eq).resolve_right x_ne

end

section

variable {ι ι' R R₂ M M' : Type*}

variable {v : ι → M}

variable [Ring R] [CommRing R₂] [AddCommGroup M]

variable [Module R M] [Module R₂ M]

variable {x y : M}

variable (b : Basis ι R M)

variable {M R : Type*} [Ring R] [Nontrivial R] [IsAddTorsionFree R]
  [AddCommGroup M] [Module R M] (A : AddSubgroup M) {ι : Type*} (b : Basis ι R M)

theorem addSubgroupOfClosure_apply (h : A = .closure (Set.range b)) (i : ι) :
    b.addSubgroupOfClosure A h i = b i := by
  simp [Module.Basis.addSubgroupOfClosure]

end

section

variable {ι ι' R R₂ M M' : Type*}

variable {v : ι → M}

variable [Ring R] [CommRing R₂] [AddCommGroup M]

variable [Module R M] [Module R₂ M]

variable {x y : M}

variable (b : Basis ι R M)

variable {M R : Type*} [Ring R] [Nontrivial R] [IsAddTorsionFree R]
  [AddCommGroup M] [Module R M] (A : AddSubgroup M) {ι : Type*} (b : Basis ι R M)

theorem addSubgroupOfClosure_repr_apply (h : A = .closure (Set.range b)) (x : A) (i : ι) :
    (b.addSubgroupOfClosure A h).repr x i = b.repr x i := by
  suffices Finsupp.mapRange.linearMap (Algebra.linearMap ℤ R) ∘ₗ
      (b.addSubgroupOfClosure A h).repr.toLinearMap =
        ((b.repr : M →ₗ[R] ι →₀ R).restrictScalars ℤ).domRestrict A.toIntSubmodule by
    exact DFunLike.congr_fun (LinearMap.congr_fun this x) i
  exact (b.addSubgroupOfClosure A h).ext fun _ ↦ by simp

end

section

variable {ι ι' R R₂ M M' : Type*}

variable {v : ι → M}

variable [Ring R] [CommRing R₂] [AddCommGroup M]

variable [Module R M] [Module R₂ M]

variable {x y : M}

variable (b : Basis ι R M)

theorem mem_center_iff {A}
    [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [SMulCommClass R A A] [SMulCommClass R R A] [IsScalarTower R A A]
    (b : Module.Basis ι R A) {z : A} :
    z ∈ Set.center A ↔
      (∀ i, Commute (b i) z) ∧ ∀ i j,
        z * (b i * b j) = (z * b i) * b j
          ∧ (b i * b j) * z = b i * (b j * z) := by
  constructor
  · intro h
    constructor
    · intro i
      apply (h.1 (b i)).symm
    · intros
      exact ⟨h.2 _ _, h.3 _ _⟩
  · intro h
    rw [center, mem_setOf_eq]
    constructor
    case comm =>
      intro y
      rw [← b.linearCombination_repr y, linearCombination_apply, sum, commute_iff_eq,
        Finset.sum_mul, Finset.mul_sum]
      simp_rw [mul_smul_comm, smul_mul_assoc, (h.1 _).eq]
    case left_assoc =>
      intro c d
      rw [← b.linearCombination_repr c, ← b.linearCombination_repr d, linearCombination_apply,
          linearCombination_apply, sum, sum, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum,
          Finset.mul_sum]
      simp_rw [smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, Finset.mul_sum,
        Finset.smul_sum, smul_mul_assoc, mul_smul_comm, (h.2 _ _).1,
        (@SMulCommClass.smul_comm R R A)]
      rw [Finset.sum_comm]
    case right_assoc =>
      intro c d
      rw [← b.linearCombination_repr c, ← b.linearCombination_repr d, linearCombination_apply,
          linearCombination_apply, sum, Finsupp.sum, Finset.sum_mul]
      simp_rw [smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, Finset.mul_sum,
               Finset.smul_sum, smul_mul_assoc, mul_smul_comm, Finset.sum_mul, smul_mul_assoc,
               (h.2 _ _).2]

end

section

variable {ι ι' R R₂ M M' : Type*}

variable {v : ι → M}

variable [Ring R] [CommRing R₂] [AddCommGroup M]

variable [Module R M] [Module R₂ M]

variable {x y : M}

variable (b : Basis ι R M)

variable {S : Type*} [CommRing R] [IsDomain R] [Ring S] [Nontrivial S] [AddCommGroup M]

variable [Algebra R S] [Module S M] [Module R M]

variable [IsScalarTower R S M] [IsTorsionFree R S] (b : Basis ι S M)

theorem mem_span_iff_repr_mem (m : M) :
    m ∈ span R (Set.range b) ↔ ∀ i, b.repr m i ∈ Set.range (algebraMap R S) := by
  refine
    ⟨fun hm i => ⟨(b.restrictScalars R).repr ⟨m, hm⟩ i, Module.Basis.restrictScalars_repr_apply b R ⟨m, hm⟩ i⟩,
      fun h => ?_⟩
  rw [← b.linearCombination_repr m, Finsupp.linearCombination_apply S _]
  refine sum_mem fun i _ => ?_
  obtain ⟨_, h⟩ := h i
  simp_rw [← h, algebraMap_smul]
  exact smul_mem _ _ (subset_span (Set.mem_range_self i))

end

section

variable {ι ι' R R₂ M M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable (b : Basis ι R M)

theorem mem_submodule_iff' [Fintype ι] {P : Submodule R M} (b : Module.Basis ι R P) {x : M} :
    x ∈ P ↔ ∃ c : ι → R, x = ∑ i, c i • (b i : M) := Module.Basis.mem_submodule_iff b.trans <|
    Finsupp.equivFunOnFinite.exists_congr_left.trans <|
      exists_congr fun c => by simp [Finsupp.sum_fintype, Finsupp.equivFunOnFinite]

end

section

variable {ι ι' R R₂ M M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable (b : Basis ι R M)

theorem mem_submodule_iff {P : Submodule R M} (b : Module.Basis ι R P) {x : M} :
    x ∈ P ↔ ∃ c : ι →₀ R, x = Finsupp.sum c fun i x => x • (b i : M) := by
  conv_lhs =>
    rw [← P.range_subtype, ← Submodule.map_top, ← b.span_eq, Submodule.map_span, ← Set.range_comp,
        ← Finsupp.range_linearCombination]
  simp [@eq_comm _ x, Function.comp, Finsupp.linearCombination_apply]

end

section

variable {ι ι' R R₂ M M' : Type*}

variable {v : ι → M}

variable [Ring R] [CommRing R₂] [AddCommGroup M]

variable [Module R M] [Module R₂ M]

variable {x y : M}

variable (b : Basis ι R M)

variable {S : Type*} [CommRing R] [IsDomain R] [Ring S] [Nontrivial S] [AddCommGroup M]

variable [Algebra R S] [Module S M] [Module R M]

variable [IsScalarTower R S M] [IsTorsionFree R S] (b : Basis ι S M)

theorem restrictScalars_apply (i : ι) : (b.restrictScalars R i : M) = b i := by
  simp only [Module.Basis.restrictScalars, Module.Basis.span_apply]

end

section

variable {ι ι' R R₂ M M' : Type*}

variable {v : ι → M}

variable [Ring R] [CommRing R₂] [AddCommGroup M]

variable [Module R M] [Module R₂ M]

variable {x y : M}

variable (b : Basis ι R M)

variable {S : Type*} [CommRing R] [IsDomain R] [Ring S] [Nontrivial S] [AddCommGroup M]

variable [Algebra R S] [Module S M] [Module R M]

variable [IsScalarTower R S M] [IsTorsionFree R S] (b : Basis ι S M)

theorem restrictScalars_repr_apply (m : span R (Set.range b)) (i : ι) :
    algebraMap R S ((b.restrictScalars R).repr m i) = b.repr m i := by
  suffices
    Finsupp.mapRange.linearMap (Algebra.linearMap R S) ∘ₗ (b.restrictScalars R).repr.toLinearMap =
      ((b.repr : M →ₗ[S] ι →₀ S).restrictScalars R).domRestrict _
    by exact DFunLike.congr_fun (LinearMap.congr_fun this m) i
  refine Module.Basis.ext (b.restrictScalars R) fun _ => ?_
  simp only [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply, map_one,
    Module.Basis.repr_self, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
    Algebra.linearMap_apply, LinearMap.domRestrict_apply,
    Module.Basis.restrictScalars_apply, LinearMap.coe_restrictScalars]

end
