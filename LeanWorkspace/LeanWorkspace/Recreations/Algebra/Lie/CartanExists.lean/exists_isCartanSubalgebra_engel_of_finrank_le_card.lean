import Mathlib

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]

theorem exists_isCartanSubalgebra_engel_of_finrank_le_card (h : finrank K L ≤ #K) :
    ∃ x : L, IsCartanSubalgebra (engel K x) := by
  obtain ⟨x, hx⟩ := exists_isRegular_of_finrank_le_card K L h
  use x
  refine ⟨?_, normalizer_engel _ _⟩
  apply isNilpotent_of_forall_le_engel
  intro y hy
  set Ex : {engel K z | z ∈ engel K x} := ⟨engel K x, x, self_mem_engel _ _, rfl⟩
  suffices IsBot Ex from @this ⟨engel K y, y, hy, rfl⟩
  apply LieAlgebra.engel_isBot_of_isMin h (engel K x) Ex le_rfl
  rintro ⟨_, y, hy, rfl⟩ hyx
  suffices finrank K (engel K x) ≤ finrank K (engel K y) by
    suffices engel K y = engel K x from this.ge
    apply LieSubalgebra.toSubmodule_injective
    exact Submodule.eq_of_le_of_finrank_le hyx this
  rw [(isRegular_iff_finrank_engel_eq_rank K x).mp hx]
  apply rank_le_finrank_engel

