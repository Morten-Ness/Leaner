import Mathlib

variable {R : Type u} [CommSemiring R] (S : Submonoid R)

variable (M : Type v) [AddCommMonoid M] [Module R M]

variable (T : Type*) [CommSemiring T] [Algebra R T] [IsLocalization S T]

theorem r.isEquiv : IsEquiv _ (LocalizedModule.r S M) := { refl := fun ⟨m, s⟩ => ⟨1, by rw [one_smul]⟩
    trans := fun ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨m3, s3⟩ ⟨u1, hu1⟩ ⟨u2, hu2⟩ => by
      use u1 * u2 * s2
      -- Put everything in the same shape, sorting the terms using `simp`
      have hu1' := congr_arg ((u2 * s3) • ·) hu1.symm
      have hu2' := congr_arg ((u1 * s1) • ·) hu2.symm
      simp only [← mul_smul, mul_comm, mul_left_comm] at hu1' hu2' ⊢
      rw [hu2', hu1']
    symm := fun ⟨_, _⟩ ⟨_, _⟩ ⟨u, hu⟩ => ⟨u, hu.symm⟩ }

