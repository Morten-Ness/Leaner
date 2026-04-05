import Mathlib

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem normalizer_engel (x : L) : normalizer (LieSubalgebra.engel R x) = LieSubalgebra.engel R x := by
  apply le_antisymm _ (le_normalizer _)
  intro y hy
  rw [mem_normalizer_iff] at hy
  specialize hy x (LieSubalgebra.self_mem_engel R x)
  rw [← lie_skew, neg_mem_iff (G := L), LieSubalgebra.mem_engel_iff] at hy
  rcases hy with ⟨n, hn⟩
  rw [LieSubalgebra.mem_engel_iff]
  use n + 1
  rw [pow_succ, Module.End.mul_apply]
  exact hn

