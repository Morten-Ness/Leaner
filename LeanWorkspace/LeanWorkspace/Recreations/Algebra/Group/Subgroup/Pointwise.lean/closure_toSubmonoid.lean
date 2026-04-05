import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem closure_toSubmonoid (S : Set G) :
    (closure S).toSubmonoid = Submonoid.closure (S ∪ S⁻¹) := by
  refine le_antisymm (fun x hx => ?_) (Submonoid.closure_le.2 ?_)
  · refine
      closure_induction
        (fun x hx => Submonoid.closure_mono subset_union_left (Submonoid.subset_closure hx))
        (Submonoid.one_mem _) (fun x y _ _ hx hy => Submonoid.mul_mem _ hx hy) (fun x _ hx => ?_) hx
    rwa [← Submonoid.mem_closure_inv, Set.union_inv, inv_inv, Set.union_comm]
  · simp only [true_and, coe_toSubmonoid, union_subset_iff, subset_closure, Subgroup.inv_subset_closure]

