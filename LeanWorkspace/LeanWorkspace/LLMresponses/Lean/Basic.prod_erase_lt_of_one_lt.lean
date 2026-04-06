FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_erase_lt_of_one_lt {κ : Type*} [DecidableEq ι] [CommMonoid κ] [LT κ]
    [Covariant κ κ (fun x y => x * y) (· < ·)] {s : Finset ι} {d : ι} (hd : d ∈ s)
    {f : ι → κ} (hdf : 1 < f d) : ∏ m ∈ s.erase d, f m < ∏ m ∈ s, f m := by
  classical
  simpa [Finset.prod_erase_mul _ _ hd, mul_comm, one_mul] using
    show 1 * ∏ m ∈ s.erase d, f m < f d * ∏ m ∈ s.erase d, f m from
      mul_lt_mul_of_lt_left' hdf (∏ m ∈ s.erase d, f m)
