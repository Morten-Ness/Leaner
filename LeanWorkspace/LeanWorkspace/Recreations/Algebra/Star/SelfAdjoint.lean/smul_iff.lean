import Mathlib

variable {R A : Type*}

theorem smul_iff [Monoid R] [StarMul R] [Star A]
    [MulAction R A] [StarModule R A] {r : R} (hr : IsSelfAdjoint r) (hu : IsUnit r) {x : A} :
    IsSelfAdjoint (r • x) ↔ IsSelfAdjoint x := by
  refine ⟨fun hrx ↦ ?_, .smul hr⟩
  lift r to Rˣ using hu
  rw [← inv_smul_smul r x]
  replace hr : IsSelfAdjoint r := Units.ext IsSelfAdjoint.star_eq hr
  exact IsSelfAdjoint.smul IsSelfAdjoint.inv hr hrx

