import Mathlib

section

variable {ι R R₂ M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable [CommSemiring R₂] [Module R₂ M]

theorem coord_unitsSMul (e : Module.Basis ι R₂ M) (w : ι → R₂ˣ) (i : ι) :
    (Module.Basis.unitsSMul e w).coord i = (w i)⁻¹ • e.coord i := by
  classical
    apply e.ext
    intro j
    trans ((Module.Basis.unitsSMul e w).coord i) ((w j)⁻¹ • (Module.Basis.unitsSMul e w) j)
    · simp [Module.Basis.unitsSMul, ← mul_smul]
    simp only [Module.Basis.coord_apply, LinearMap.smul_apply, Module.Basis.repr_self, Units.smul_def,
      map_smul, Finsupp.single_apply]
    split_ifs with h <;> simp [h]

end

section

variable {ι R R₂ M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] (b : Basis ι R M)

variable {v : ι → M} {x y : M}

theorem groupSMul_apply {G : Type*} [Group G] [DistribMulAction G R] [DistribMulAction G M]
    [IsScalarTower G R M] [SMulCommClass G R M] {v : Module.Basis ι R M} {w : ι → G} (i : ι) :
    v.groupSMul w i = (w • (v : ι → M)) i := mk_apply (LinearIndependent.group_smul v.linearIndependent w)
    (Module.Basis.groupSMul_span_eq_top v.span_eq).ge i

end

section

variable {ι R R₂ M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] (b : Basis ι R M)

variable {v : ι → M} {x y : M}

theorem groupSMul_span_eq_top {G : Type*} [Group G] [SMul G R] [MulAction G M]
    [IsScalarTower G R M] {v : ι → M} (hv : Submodule.span R (Set.range v) = ⊤) {w : ι → G} :
    Submodule.span R (Set.range (w • v)) = ⊤ := by
  rw [eq_top_iff]
  intro j hj
  rw [← hv] at hj
  rw [Submodule.mem_span] at hj ⊢
  refine fun p hp => hj p fun u hu => ?_
  obtain ⟨i, rfl⟩ := hu
  have : ((w i)⁻¹ • (1 : R)) • w i • v i ∈ p := p.smul_mem ((w i)⁻¹ • (1 : R)) (hp ⟨i, rfl⟩)
  rwa [smul_one_smul, inv_smul_smul] at this

end

section

variable {ι R R₂ M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable [CommSemiring R₂] [Module R₂ M]

theorem repr_isUnitSMul {v : Module.Basis ι R₂ M} {w : ι → R₂} (hw : ∀ i, IsUnit (w i)) (x : M) (i : ι) :
    (v.isUnitSMul hw).repr x i = (hw i).unit⁻¹ • v.repr x i := Module.Basis.repr_unitsSMul _ _ _ _

end

section

variable {ι R R₂ M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable [CommSemiring R₂] [Module R₂ M]

theorem repr_unitsSMul (e : Module.Basis ι R₂ M) (w : ι → R₂ˣ) (v : M) (i : ι) :
    (e.unitsSMul w).repr v i = (w i)⁻¹ • e.repr v i := congr_arg (fun f : M →ₗ[R₂] R₂ => f v) (Module.Basis.coord_unitsSMul e w i)

end

section

variable {ι R R₂ M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] (b : Basis ι R M)

variable {v : ι → M} {x y : M}

theorem unitsSMul_apply {v : Module.Basis ι R M} {w : ι → Rˣ} (i : ι) : Module.Basis.unitsSMul v w i = w i • v i := mk_apply (LinearIndependent.units_smul v.linearIndependent w)
    (Module.Basis.units_smul_span_eq_top v.span_eq).ge i

end

section

variable {ι R R₂ M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] (b : Basis ι R M)

variable {v : ι → M} {x y : M}

theorem units_smul_span_eq_top {v : ι → M} (hv : Submodule.span R (Set.range v) = ⊤) {w : ι → Rˣ} :
    Submodule.span R (Set.range (w • v)) = ⊤ := Module.Basis.groupSMul_span_eq_top hv

end
