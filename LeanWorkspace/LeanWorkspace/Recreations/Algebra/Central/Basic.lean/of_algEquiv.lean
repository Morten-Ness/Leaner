import Mathlib

variable (K : Type u) [CommSemiring K] (D D' : Type v) [Semiring D] [Algebra K D]
  [h : IsCentral K D] [Semiring D'] [Algebra K D']

theorem of_algEquiv (e : D ≃ₐ[K] D') : Algebra.IsCentral K D' where
  out x hx := have ⟨k, hk⟩ := h.1 ((MulEquivClass.apply_mem_center_iff e.symm).mpr hx)
    ⟨k, by simpa [ofId] using congr(e $hk)⟩

