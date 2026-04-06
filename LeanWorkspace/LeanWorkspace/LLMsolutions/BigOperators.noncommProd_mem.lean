FAIL
import Mathlib

variable {M A B : Type*}

variable [Monoid M] {x : M} (s : Submonoid M)

theorem noncommProd_mem (S : Submonoid M) {ι : Type*} (t : Finset ι) (f : ι → M) (comm)
    (h : ∀ c ∈ t, f c ∈ S) : t.noncommProd f comm ∈ S := by
  classical
  simpa [Finset.noncommProd] using
    (show ((t.1.map f).prod ∈ S) from by
      refine List.prod_mem ?_
      intro y hy
      rcases List.mem_map.mp hy with ⟨c, hc, rfl⟩
      exact h c hc)
