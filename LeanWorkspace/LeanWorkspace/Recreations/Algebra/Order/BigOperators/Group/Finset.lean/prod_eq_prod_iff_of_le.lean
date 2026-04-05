import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [Preorder M] [IsOrderedCancelMonoid M] {f g : ι → M} {s t : Finset ι}

theorem prod_eq_prod_iff_of_le {ι M : Type*} [CommMonoid M] [PartialOrder M]
  [IsOrderedCancelMonoid M] {s : Finset ι} {f g : ι → M} (h : ∀ i ∈ s, f i ≤ g i) :
    ((∏ i ∈ s, f i) = ∏ i ∈ s, g i) ↔ ∀ i ∈ s, f i = g i := by
  classical
    revert h
    refine Finset.induction_on s (fun _ ↦ ⟨fun _ _ h ↦ False.elim (Finset.notMem_empty _ h),
      fun _ ↦ rfl⟩) fun a s ha ih H ↦ ?_
    specialize ih fun i ↦ H i ∘ Finset.mem_insert_of_mem
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.forall_mem_insert, ← ih]
    exact
      mul_eq_mul_iff_eq_and_eq (H a (s.mem_insert_self a))
        (Finset.prod_le_prod' fun i ↦ H i ∘ Finset.mem_insert_of_mem)

