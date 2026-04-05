import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem orderTop_eq_archimedeanClassMk [IsOrderedAddMonoid R] [Archimedean R] (x : f.val.domain) :
    FiniteArchimedeanClass.withTopOrderIso M (ofLex (f.val x)).orderTop = .mk x.val := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hx0' : x.val ≠ 0 := by simpa using hx0
  -- Pick a representative `x'` from `stratum` with the same class as `x`.
  -- `f.val x'` is a `HahnSeries.single` whose `orderTop` is known
  obtain ⟨⟨x', hx'mem⟩, hx'0⟩ := exists_ne (0 : seed.stratum (.mk x hx0'))
  have heq : ArchimedeanClass.mk x' = .mk x.val := by
    apply HahnEmbedding.ArchimedeanStrata.archimedeanClassMk_of_mem_stratum seed hx'mem
    simpa using hx'0
  let x'' : f.val.domain := ⟨x', HahnEmbedding.Partial.mem_domain f hx'mem⟩
  have hx''mem : x''.val ∈ seed.stratum (HahnEmbedding.Partial.mk x.val hx0') := hx'mem
  have h0 : (seed.coeff (HahnEmbedding.Partial.mk x.val hx0')) ⟨x''.val, hx''mem⟩ ≠ 0 := by
    rw [(LinearMap.map_eq_zero_iff _ (seed.strictMono_coeff _).injective).ne]
    unfold x''
    simpa using hx'0
  have heq' : ArchimedeanClass.mk x''.val = .mk x.val := heq
  rw [← HahnEmbedding.Partial.orderTop_eq_iff, HahnEmbedding.Partial.apply_of_mem_stratum f hx''mem, ofLex_toLex,
    HahnSeries.orderTop_single h0] at heq'
  simp [← heq']

