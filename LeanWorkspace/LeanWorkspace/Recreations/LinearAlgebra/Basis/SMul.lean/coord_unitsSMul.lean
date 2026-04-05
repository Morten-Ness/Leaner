import Mathlib

variable {ι R R₂ M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] (b : Basis ι R M)

variable {v : ι → M} {x y : M}

variable [CommSemiring R₂] [Module R₂ M]

theorem coord_unitsSMul (e : Module.Basis ι R₂ M) (w : ι → R₂ˣ) (i : ι) :
    (Module.Basis.unitsSMul e w).coord i = (w i)⁻¹ • e.coord i := by
  classical
    apply e.ext
    intro j
    trans ((Module.Basis.unitsSMul e w).coord i) ((w j)⁻¹ • (Module.Basis.unitsSMul e w) j)
    · simp [Module.Basis.unitsSMul, ← mul_smul]
    simp only [Module.Basis.coord_apply, LinearMap.smul_apply, Module.Basis.repr_self, Units.smul_def,
      map_smul, Finsupp.single_apply]
    split_ifs with h <;> simp [h]

