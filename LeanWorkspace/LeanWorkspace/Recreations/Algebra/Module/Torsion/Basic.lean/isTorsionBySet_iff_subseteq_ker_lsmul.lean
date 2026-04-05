import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem isTorsionBySet_iff_subseteq_ker_lsmul :
    IsTorsionBySet R M s ↔ s ⊆ LinearMap.ker (LinearMap.lsmul R M) where
  mp h r hr := LinearMap.mem_ker.mpr <| LinearMap.ext fun x => @h x ⟨r, hr⟩
  mpr | h, x, ⟨_, hr⟩ => DFunLike.congr_fun (LinearMap.mem_ker.mp (h hr)) x

