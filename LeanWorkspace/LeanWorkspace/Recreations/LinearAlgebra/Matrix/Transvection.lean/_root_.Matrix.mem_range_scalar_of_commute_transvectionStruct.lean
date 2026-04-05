import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R n} (i j : n)

variable [Fintype n]

theorem _root_.Matrix.mem_range_scalar_of_commute_transvectionStruct {M : Matrix n n R}
    (hM : ∀ t : Matrix.TransvectionStruct n R, Commute t.toMatrix M) :
    M ∈ Set.range (Matrix.scalar n) := by
  refine mem_range_scalar_of_commute_single ?_
  intro i j hij
  simpa [Matrix.transvection, mul_add, add_mul] using (hM ⟨i, j, hij, 1⟩).eq

