import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem apply_of_mem_stratum {x : f.val.domain} {c : FiniteArchimedeanClass M}
    (hx : x.val ∈ seed.stratum c) :
    f.val x = toLex (HahnSeries.single c (seed.coeff c ⟨x.val, hx⟩)) := by
  have hx' : x.val ∈ seed.baseEmbedding.domain := HahnEmbedding.Seed.mem_domain_baseEmbedding seed hx
  have heq : (⟨x.val, hx'⟩ : seed.baseEmbedding.domain).val = x.val := rfl
  rw [← f.prop.baseEmbedding_le.2 heq]
  let fx : Π₀ c, seed.stratum c := DFinsupp.single c ⟨x.val, hx⟩
  have hfx : x.val = fx.sum fun c ↦ (seed.stratum c).subtype := by
    simp [fx, DFinsupp.sum_single_index]
  apply_fun ofLex
  rw [ofLex_toLex]
  ext d
  rw [HahnEmbedding.Seed.coeff_baseEmbedding seed hfx]
  unfold fx
  obtain rfl | hdc := eq_or_ne d c
  · simp
  simp [HahnSeries.coeff_single_of_ne hdc, hdc.symm]

