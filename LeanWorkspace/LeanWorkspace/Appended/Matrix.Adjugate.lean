import Mathlib

section

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem IsSymm.adjugate {A : Matrix n n α} (hA : A.IsSymm) : A.adjugate.IsSymm := by
  rw [Matrix.IsSymm, Matrix.adjugate_transpose, hA.eq]

end

section

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_eq_one_of_card_eq_one {A : Matrix n n α} (h : Fintype.card n = 1) :
    Matrix.adjugate A = 1 := haveI : Subsingleton n := Fintype.card_le_one_iff_subsingleton.mp h.le
  Matrix.adjugate_subsingleton _

end

section

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_fin_two (A : Matrix (Fin 2) (Fin 2) α) :
    Matrix.adjugate A = !![A 1 1, -A 0 1; -A 1 0, A 0 0] := by
  ext i j
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  fin_cases i <;> fin_cases j <;> simp

end

section

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_one : Matrix.adjugate (1 : Matrix n n α) = 1 := by
  ext
  simp [Matrix.adjugate_def, Matrix.one_apply, Pi.single_apply, eq_comm]

end

section

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_pow (A : Matrix n n α) (k : ℕ) : Matrix.adjugate (A ^ k) = Matrix.adjugate A ^ k := by
  induction k with
  | zero => simp
  | succ k IH => rw [pow_succ', Matrix.adjugate_mul_distrib, IH, pow_succ]

end

section

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

variable (A : Matrix n n α) (b : n → α)

theorem cramer_is_linear : IsLinearMap α (Matrix.cramerMap A) := by
  constructor <;> intros <;> ext i
  · apply (Matrix.cramerMap_is_linear A i).1
  · apply (Matrix.cramerMap_is_linear A i).2

end

section

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

variable (A : Matrix n n α) (b : n → α)

theorem cramer_one : Matrix.cramer (1 : Matrix n n α) = 1 := by
  ext i j
  convert congr_fun (Matrix.cramer_row_self (1 : Matrix n n α) (Pi.single i 1) i _) j
  · simp
  · intro j
    rw [Matrix.one_eq_pi_single, Pi.single_comm]

end

section

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

variable (A : Matrix n n α) (b : n → α)

theorem cramer_smul (r : α) (A : Matrix n n α) :
    Matrix.cramer (r • A) = r ^ (Fintype.card n - 1) • Matrix.cramer A := LinearMap.ext fun _ => funext fun _ => det_updateCol_smul_left _ _ _ _

end

section

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem isRegular_of_isLeftRegular_det {A : Matrix n n α} (hA : IsLeftRegular A.det) :
    IsRegular A := by
  constructor
  · intro B Polynomial.C h
    refine hA.matrix ?_
    simp only at h ⊢
    rw [← Matrix.one_mul B, ← Matrix.one_mul Polynomial.C, ← Matrix.smul_mul, ← Matrix.smul_mul, ←
      Matrix.adjugate_mul, Matrix.mul_assoc, Matrix.mul_assoc, h]
  · intro B Polynomial.C (h : B * A = Polynomial.C * A)
    refine hA.matrix ?_
    simp only
    rw [← Matrix.mul_one B, ← Matrix.mul_one Polynomial.C, ← Matrix.mul_smul, ← Matrix.mul_smul, ←
      Matrix.mul_adjugate, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h]

end

section

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

variable (A : Matrix n n α) (b : n → α)

theorem sum_cramer {β} (s : Finset β) (f : β → n → α) :
    (∑ x ∈ s, Matrix.cramer A (f x)) = Matrix.cramer A (∑ x ∈ s, f x) := (map_sum (Matrix.cramer A) ..).symm

end

section

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

variable (A : Matrix n n α) (b : n → α)

theorem sum_cramer_apply {β} (s : Finset β) (f : n → β → α) (i : n) :
    (∑ x ∈ s, Matrix.cramer A (fun j => f j x) i) = Matrix.cramer A (fun j : n => ∑ x ∈ s, f j x) i := calc
    (∑ x ∈ s, Matrix.cramer A (fun j => f j x) i) = (∑ x ∈ s, Matrix.cramer A fun j => f j x) i :=
      (Finset.sum_apply i s _).symm
    _ = Matrix.cramer A (fun j : n => ∑ x ∈ s, f j x) i := by
      rw [Matrix.sum_cramer, Matrix.cramer_apply]
      congr with j
      apply Finset.sum_apply

end
