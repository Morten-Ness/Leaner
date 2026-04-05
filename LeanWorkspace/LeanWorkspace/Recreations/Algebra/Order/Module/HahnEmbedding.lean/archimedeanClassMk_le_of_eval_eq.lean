import Mathlib

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

variable (seed : Seed K M R)

variable {seed} (f : Partial seed)

set_option backward.isDefEq.respectTransparency false in
theorem archimedeanClassMk_le_of_eval_eq [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    {y : f.val.domain} (h : f.eval x = f.val y) (z : f.val.domain) :
    ArchimedeanClass.mk (x - z.val) ≤ .mk (x - y.val) := by
  have : x - y.val = x - z.val + (z.val - y.val) := by abel
  rw [this]
  apply ArchimedeanClass.mk_left_le_mk_add
  by_cases hyz : z.val - y.val = 0
  · simp [hyz]
  have h1 (c : FiniteArchimedeanClass M) (hc : c.val < .mk (x - z.val)) :
      (ofLex (f.eval x)).coeff c = (ofLex (f.val z)).coeff c := by
    rw [ArchimedeanClass.mk_sub_comm] at hc
    simp_rw [HahnEmbedding.Partial.eval, ofLex_toLex]
    apply HahnEmbedding.Partial.evalCoeff_eq
    simpa [c.prop] using fun _ ↦ hc
  have h2 : ∀ c : FiniteArchimedeanClass M, c.val < .mk (x - z.val) →
      (ofLex (f.val (z - y))).coeff c = 0 := by
    intro c hc
    rw [LinearPMap.map_sub, ofLex_sub, HahnSeries.coeff_sub, sub_eq_zero, ← h]
    exact (h1 c hc).symm
  contrapose! h2
  exact ⟨FiniteArchimedeanClass.mk (z.val - y.val) hyz, h2, HahnEmbedding.Partial.coeff_ne_zero _ _⟩

