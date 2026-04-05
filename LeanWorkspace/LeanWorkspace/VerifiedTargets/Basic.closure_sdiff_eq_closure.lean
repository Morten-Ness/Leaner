import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

variable {t : Set M}

theorem closure_sdiff_eq_closure (hts : t ⊆ Submonoid.closure (s \ t)) : Submonoid.closure (s \ t) = Submonoid.closure s := by
  refine (Submonoid.closure_mono Set.diff_subset).antisymm <| Submonoid.closure_le.mpr <| fun x hxs ↦ ?_
  by_cases hxt : x ∈ t
  · exact hts hxt
  · rw [SetLike.mem_coe, Submonoid.mem_closure]
    exact fun N hN ↦ hN <| Set.mem_diff_of_mem hxs hxt

