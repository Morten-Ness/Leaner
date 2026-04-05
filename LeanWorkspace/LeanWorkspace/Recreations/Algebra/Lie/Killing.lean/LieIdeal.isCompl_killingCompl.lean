import Mathlib

variable (R K L : Type*) [CommRing R] [Field K] [LieRing L] [LieAlgebra R L] [LieAlgebra K L]

set_option backward.isDefEq.respectTransparency false in
theorem LieIdeal.isCompl_killingCompl [IsKilling K L] [Module.Finite K L] (I : LieIdeal K L) :
    IsCompl I I.killingCompl := by
  suffices Disjoint I I.killingCompl by
    rwa [← LieSubmodule.isCompl_toSubmodule, I.toSubmodule_killingCompl,
      LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint (LieModule.traceForm_isSymm K L L).isRefl,
      ← I.toSubmodule_killingCompl, LieSubmodule.disjoint_toSubmodule]
  suffices IsLieAbelian (I ⊓ I.killingCompl : LieIdeal K L) by
    rw [disjoint_iff]
    exact IsKilling.ideal_eq_bot_of_isLieAbelian _
  suffices ∀ (x y z : L) (hx : x ∈ killingCompl K L I) (hy : y ∈ I),
      LieModule.traceForm K L L ⁅x, y⁆ z = 0 by
    rw [LieSubmodule.lie_abelian_iff_lie_self_eq_bot, LieSubmodule.lie_eq_bot_iff]
    rintro x ⟨-, hx⟩ y ⟨hy, -⟩
    exact (IsKilling.killingForm_nondegenerate K L).1 _ fun z ↦ this x y z hx hy
  intro x y z hx hy
  rw [LieModule.traceForm_apply_lie_apply K L L x y z, LieModule.traceForm_comm K L L]
  exact I.mem_killingCompl.mp hx _ <| lie_mem_left K L I y z hy

