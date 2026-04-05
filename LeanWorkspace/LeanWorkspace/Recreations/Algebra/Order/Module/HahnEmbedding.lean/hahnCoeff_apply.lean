import Mathlib

open scoped DirectSum

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

theorem hahnCoeff_apply {x : seed.baseDomain} {f : Π₀ c, seed.stratum c}
    (h : x.val = f.sum fun c ↦ (seed.stratum c).subtype) (c : FiniteArchimedeanClass M) :
    seed.hahnCoeff x c = seed.coeff c (f c) := by
  suffices seed.baseDomain.subtype.submoduleComap
      (seed.stratum c) (DirectSum.decompose seed.stratum' x c) = f c by
    simp [HahnEmbedding.Seed.hahnCoeff, HahnEmbedding.Seed.coeff', decomposeLinearEquiv_apply, this]
  have hxm {c : FiniteArchimedeanClass M} (x : seed.stratum c) : x.val ∈ seed.baseDomain := by
    apply Set.mem_of_mem_of_subset x.prop
    simpa using le_iSup _ _
  let f' : ⨁ c, seed.stratum' c :=
    f.mapRange (fun c x ↦ (⟨⟨x.val, hxm x⟩, by simp⟩ : seed.stratum' c)) (by simp)
  have hf : f c = (seed.baseDomain.subtype.submoduleComap (seed.stratum c)) (f' c) := by
    apply Subtype.ext
    simp [f']
  have hx : x = (decompose seed.stratum').symm f' := by
    change x = f'.coeAddMonoidHom _
    apply Submodule.subtype_injective
    rw [DirectSum.coeAddMonoidHom_eq_dfinsuppSum, DFinsupp.sum_mapRange_index (by simp)]
    simp [h]
  simp [hf, hx]

