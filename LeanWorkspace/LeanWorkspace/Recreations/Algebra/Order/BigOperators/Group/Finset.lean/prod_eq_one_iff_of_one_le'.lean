import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [CommMonoid N] [Preorder N]

variable {f g : ι → N} {s t : Finset ι}

theorem prod_eq_one_iff_of_one_le' {ι : Type u_1} {N : Type u_5} [CommMonoid N] [PartialOrder N]
    {f : ι → N} {s : Finset ι} [MulLeftMono N] :
    (∀ i ∈ s, 1 ≤ f i) → ((∏ i ∈ s, f i) = 1 ↔ ∀ i ∈ s, f i = 1) := by
  classical
    refine Finset.induction_on s
      (fun _ ↦ ⟨fun _ _ h ↦ False.elim (Finset.notMem_empty _ h), fun _ ↦ rfl⟩) ?_
    intro a s ha ih H
    have : ∀ i ∈ s, 1 ≤ f i := fun _ ↦ H _ ∘ mem_insert_of_mem
    rw [prod_insert ha, mul_eq_one_iff_of_one_le (H _ <| mem_insert_self _ _) (Finset.one_le_prod' this),
      forall_mem_insert, ih this]

