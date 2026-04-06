import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem noncommProd_mem (K : Subgroup G) {ι : Type*} {t : Finset ι} {f : ι → G} (comm) :
    (∀ c ∈ t, f c ∈ K) → t.noncommProd f comm ∈ K := by
  intro hf
  simpa using K.noncommProd_mem comm hf
