import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_erase_lt_of_one_lt {κ : Type*} [DecidableEq ι] [CommMonoid κ] [LT κ]
    [MulLeftStrictMono κ] {s : Finset ι} {d : ι} (hd : d ∈ s) {f : ι → κ}
    (hdf : 1 < f d) : ∏ m ∈ s.erase d, f m < ∏ m ∈ s, f m := by
  conv in ∏ m ∈ s, f m => rw [← Finset.insert_erase hd]
  rw [Finset.prod_insert (Finset.notMem_erase d s)]
  exact lt_mul_of_one_lt_left' _ hdf

