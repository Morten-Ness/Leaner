import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem single_le_finprod {M : Type*} [CommMonoid M] [Preorder M] [IsOrderedMonoid M]
    (i : α) {f : α → M}
    (hf : HasFiniteMulSupport f) (h : ∀ j, 1 ≤ f j) : f i ≤ ∏ᶠ j, f j := by
  classical calc
      f i ≤ ∏ j ∈ insert i hf.toFinset, f j :=
        Finset.single_le_prod' (fun j _ => h j) (Finset.mem_insert_self _ _)
      _ = ∏ᶠ j, f j :=
        (finprod_eq_prod_of_mulSupport_toFinset_subset _ hf (Finset.subset_insert _ _)).symm

