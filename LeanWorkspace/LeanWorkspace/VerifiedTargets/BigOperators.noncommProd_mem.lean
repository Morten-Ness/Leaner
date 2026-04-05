import Mathlib

variable {M A B : Type*}

variable [Monoid M] {x : M} (s : Submonoid M)

theorem noncommProd_mem (S : Submonoid M) {ι : Type*} (t : Finset ι) (f : ι → M) (comm)
    (h : ∀ c ∈ t, f c ∈ S) : t.noncommProd f comm ∈ S := by
  apply Submonoid.multiset_noncommProd_mem
  intro y
  rw [Multiset.mem_map]
  rintro ⟨x, ⟨hx, rfl⟩⟩
  exact h x hx

