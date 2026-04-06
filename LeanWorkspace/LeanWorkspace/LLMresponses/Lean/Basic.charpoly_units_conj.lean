FAIL
import Mathlib

variable {R S : Type*} [CommRing R] [CommRing S]

variable {m n : Type*} [DecidableEq m] [DecidableEq n] [Fintype m] [Fintype n]

variable (M₁₁ : Matrix m m R) (M₁₂ : Matrix m n R) (M₂₁ : Matrix n m R) (M₂₂ M : Matrix n n R)

variable (i j : n)

theorem charpoly_units_conj (M : (Matrix n n R)ˣ) (N : Matrix n n R) :
    (M.val * N * M⁻¹.val).charpoly = N.charpoly := by
  let P : LinearMap R (n → R) (n → R) := Matrix.toLin' N
  let e : LinearEquiv R (n → R) (n → R) := Matrix.toLin' M.val |> LinearEquiv.ofBijective ?_
  have hM : Function.Bijective (Matrix.toLin' M.val) := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have := congrArg (Matrix.toLin' M⁻¹.val) hxy
      simpa [Matrix.toLin'_mul, Matrix.mul_assoc] using this
    · intro x
      refine ⟨Matrix.toLin' M⁻¹.val x, ?_⟩
      simp [Matrix.toLin'_mul, Matrix.mul_assoc]
  let e' : LinearEquiv R (n → R) (n → R) := LinearEquiv.ofBijective (Matrix.toLin' M.val) hM
  have hconj :
      Matrix.toLin' (M.val * N * M⁻¹.val) = e'.conj P := by
    ext x i
    simp [P, e', LinearEquiv.conj_apply, Matrix.toLin'_mul, Matrix.mul_assoc]
  rw [← LinearMap.charpoly_toMatrix_basis_eq_charpoly (b := Pi.basisFun R n) (f := e'.conj P),
      ← LinearMap.charpoly_toMatrix_basis_eq_charpoly (b := Pi.basisFun R n) (f := P)]
  simp [hconj, P]
