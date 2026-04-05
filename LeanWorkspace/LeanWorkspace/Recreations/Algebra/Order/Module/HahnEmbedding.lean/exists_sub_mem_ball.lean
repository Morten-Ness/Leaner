import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem exists_sub_mem_ball [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain)
    (y : f.val.domain) :
    ∃ z : f.val.domain, z.val - x ∈ ball K (HahnEmbedding.Partial.mk _ (HahnEmbedding.Partial.val_sub_ne_zero f hx y)) := by
  set c := HahnEmbedding.Partial.mk _ (HahnEmbedding.Partial.val_sub_ne_zero f hx y)
  have hc : ArchimedeanClass.mk (y.val - x) = c := rfl
  by_contra!; apply hx
  have h := HahnEmbedding.Partial.eval_eq_truncLT f hc this
  obtain ⟨x', hx'⟩ := LinearMap.mem_range.mp (f.prop.truncLT_mem_range y c)
  rw [← hx'] at h
  contrapose! h
  exact HahnEmbedding.Partial.eval_ne f h _

