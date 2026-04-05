FAIL
import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

set_option backward.isDefEq.respectTransparency false in
theorem charpoly_sub_scalar (M : Matrix n n R) (μ : R) :
    (M - Matrix.scalar n μ).charpoly = M.charpoly.comp (Polynomial.X + Polynomial.C μ) := by
  classical
  rw [Matrix.charpoly, Matrix.charpoly]
  simp_rw [Matrix.sub_apply, Matrix.scalar_apply]
  rw [show M.map Polynomial.C - Matrix.scalar n (Polynomial.C μ) =
      M.map Polynomial.C + diagonal (fun _ => -Polynomial.C μ) by
        ext a b
        by_cases h : a = b
        · subst h
          simp
        · simp [Matrix.diagonal, h]]
  rw [Matrix.det_eq_det_finset]
  rw [Matrix.det_eq_det_finset]
  let A : Matrix n n R[X] := M.map Polynomial.C + Polynomial.X • 1
  have hA :
      M.map Polynomial.C + (Polynomial.X + Polynomial.C μ) • (1 : Matrix n n R[X]) =
        A + Polynomial.C μ • (1 : Matrix n n R[X]) := by
    ext a b
    by_cases h : a = b
    · subst h
      simp [A, add_assoc, add_left_comm, add_comm]
    · simp [A, h]
  rw [← hA]
  let e := Matrix.detMonoidHom n (R := R[X])
  change e (A + Polynomial.C μ • (1 : Matrix n n R[X])) = _
  rw [show M.charpoly.comp (Polynomial.X + Polynomial.C μ) =
      Polynomial.eval₂RingHom (Polynomial.C) (Polynomial.X + Polynomial.C μ) M.charpoly by
        rfl]
  rw [Matrix.charpoly]
  simp only [Polynomial.comp]
  rw [← RingHom.map_det]
  congr 1
  ext a b
  by_cases h : a = b
  · subst h
    simp [A, add_assoc, add_left_comm, add_comm]
  · simp [A, h]
