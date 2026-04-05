import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem eval_ne [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain)
    (y : f.val.domain) : f.eval x ≠ f.val y := by
  -- decompose `x - y = u + v`, where `v ∈ submodule (x - y)` and
  -- `u` is at higher class than `x - y`
  have := HahnEmbedding.Partial.val_sub_ne_zero f hx y
  rw [sub_ne_zero, ne_comm, ← sub_ne_zero] at this
  let xy := HahnEmbedding.Partial.mk _ this
  have hxy : x - y.val ∈ closedBall K xy := fun _ ↦ by simp; rfl
  rw [← seed.ball_sup_stratum_eq xy, Submodule.mem_sup] at hxy
  obtain ⟨u, hu, v, hv, huv⟩ := hxy
  have huv' : x - y.val - v = u := by simp [← huv]
  rw [mem_ball_iff K] at hu
  -- `z = x - u = y + v` is also in the domain.
  -- Assuming `f.eval x = f.val y` allows us to use `HahnEmbedding.Partial.archimedeanClassMk_le_of_eval_eq` on `z`
  have hyv : y.val + v ∈ f.val.domain := Submodule.add_mem _ (by simp) (HahnEmbedding.Partial.mem_domain f hv)
  by_contra! h
  obtain h := HahnEmbedding.Partial.archimedeanClassMk_le_of_eval_eq f h ⟨y.val + v, hyv⟩
  contrapose! h
  simp_rw [← sub_sub, huv']
  obtain rfl | ne := eq_or_ne u 0
  exacts [Ne.lt_top (by simpa), (mk_lt_mk ..).mp (hu ne)]

