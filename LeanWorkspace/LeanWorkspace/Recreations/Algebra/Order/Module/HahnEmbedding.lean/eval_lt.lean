import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem eval_lt [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain)
    (y : f.val.domain) (h : x < y.val) : f.eval x < f.val y := by
  -- Expand the definition of `HahnSeries`' order. We need to find the first coefficient that
  -- dictates the < relation. This coefficient is exactly at the Archimedean class of `y - x`
  rw [HahnSeries.lt_iff]
  have hxy0 : y.val - x ≠ 0 := sub_ne_zero_of_ne h.ne.symm
  refine ⟨HahnEmbedding.Partial.mk (y.val - x) hxy0, ?_, ?_⟩
  · -- All coefficients before the dictating term are the same
    intro j hj
    apply HahnEmbedding.Partial.evalCoeff_eq
    simpa [j.prop] using fun _ ↦ hj
  -- Show the dictating coefficient
  suffices f.evalCoeff x (HahnEmbedding.Partial.mk (y.val - x) hxy0) < (ofLex (f.val y)).coeff (HahnEmbedding.Partial.mk _ hxy0) by
    simpa [HahnEmbedding.Partial.eval] using this
  -- We find `z` from `f`'s domain to approximate `x`. Such approximation obeys:
  -- * `f.eval x = f.val z`
  -- * `x < y → z < y`
  -- * `HahnEmbedding.Partial.mk (x - y) = HahnEmbedding.Partial.mk (z - y)`
  obtain ⟨z, hz⟩ := HahnEmbedding.Partial.exists_sub_mem_ball f hx y
  rw [HahnEmbedding.Partial.evalCoeff_eq f hz]
  have : z ≠ x := by rintro rfl; exact hx z.2
  have hzy : z < y := by
    change z.val < y.val
    refine (sub_lt_sub_iff_right x).mp <|
      ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg ?_ (sub_nonneg_of_le h.le)
    simpa using hz (by simpa [sub_eq_zero])
  have hzyne : z.val - y.val ≠ 0 := by
    apply sub_ne_zero_of_ne
    simpa using hzy.ne
  have hzyclass : HahnEmbedding.Partial.mk (y.val - x) hxy0 = HahnEmbedding.Partial.mk (z.val - y.val) hzyne := by
    suffices ArchimedeanClass.mk (y.val - x) = .mk (z.val - y.val) by
      simpa [Subtype.ext_iff] using this
    have : y.val - z.val = y.val - x + (x - z.val) := by abel
    rw [ArchimedeanClass.mk_sub_comm z.val y.val, this]
    refine (ArchimedeanClass.mk_add_eq_mk_left ?_).symm
    rw [ArchimedeanClass.mk_sub_comm x z.val]
    simpa using hz (by simpa [sub_eq_zero])
  -- Since both `y` and `z` are in the domain, we can apply `f`'s monotonicity on them
  rw [← f.prop.strictMono.lt_iff_lt, HahnSeries.lt_iff] at hzy
  obtain ⟨i, hj, hi⟩ := hzy
  -- We show that the dictating coefficient of `f.val y < f.val z`
  -- is at the same position as the dictating coefficient of `f.eval x < f.val y`
  have hieq : i = HahnEmbedding.Partial.mk (y.val - x) hxy0 := by
    apply le_antisymm
    · by_contra! hlt
      obtain hj := sub_eq_zero_of_eq (hj (HahnEmbedding.Partial.mk _ hxy0) hlt)
      contrapose! hj
      rw [← HahnSeries.coeff_sub, ← ofLex_sub, ← LinearPMap.map_sub, hzyclass]
      apply HahnEmbedding.Partial.coeff_ne_zero f
    · contrapose! hi
      rw [hzyclass] at hi
      have hzy : z.val - y.val ∈ ball K i := fun _ ↦ hi
      exact (HahnEmbedding.Partial.coeff_eq_of_mem f y.val (by simp) hzy (by simp)).le
  exact hieq ▸ hi

