import Mathlib

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

