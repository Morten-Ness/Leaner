import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

theorem posSemidef_sum {ι : Type*} [AddLeftMono R]
    {x : ι → Matrix n n R} (s : Finset ι) (h : ∀ i ∈ s, Matrix.PosSemidef (x i)) :
    Matrix.PosSemidef (∑ i ∈ s, x i) := by
  refine ⟨isSelfAdjoint_sum s fun _ hi => h _ hi |>.1, fun y => ?_⟩
  simp [sum_apply, Finset.mul_sum, Finset.sum_mul, Finsupp.sum_finsetSum_comm,
    Finset.sum_nonneg fun _ hi => (h _ hi).2 _]

