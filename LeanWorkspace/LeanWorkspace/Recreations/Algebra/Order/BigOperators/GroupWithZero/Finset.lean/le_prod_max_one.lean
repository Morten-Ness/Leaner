import Mathlib

variable {ι R S : Type*}

variable [CommMonoidWithZero R]

variable [Preorder R] [ZeroLEOneClass R] [PosMulMono R] {f g : ι → R} {s t : Finset ι}

theorem le_prod_max_one {M : Type*} [CommMonoidWithZero M] [LinearOrder M] [ZeroLEOneClass M]
    [PosMulMono M] {i : ι} (hi : i ∈ s) (f : ι → M) :
    f i ≤ ∏ i ∈ s, max (f i) 1 := by
  classical
  rcases lt_or_ge (f i) 0 with hf | hf
  · exact (hf.trans_le <| Finset.prod_nonneg fun _ _ ↦ le_sup_of_le_right zero_le_one).le
  have : f i = ∏ j ∈ s, if i = j then f i else 1 := by
    rw [prod_eq_single_of_mem i hi fun _ _ _ ↦ by grind]
    simp
  exact this ▸ Finset.prod_le_prod (fun _ _ ↦ by grind [zero_le_one]) fun _ _ ↦ by grind

