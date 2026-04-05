import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem noncommProd_mem (K : Subgroup G) {ι : Type*} {t : Finset ι} {f : ι → G} (comm) :
    (∀ c ∈ t, f c ∈ K) → t.noncommProd f comm ∈ K := K.toSubmonoid.noncommProd_mem t f comm

