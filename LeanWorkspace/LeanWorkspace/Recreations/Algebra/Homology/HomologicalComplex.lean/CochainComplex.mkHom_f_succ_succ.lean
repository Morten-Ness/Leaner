import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable (P Q : CochainComplex V ℕ) (zero : P.X 0 ⟶ Q.X 0) (one : P.X 1 ⟶ Q.X 1)
  (one_zero_comm : zero ≫ Q.d 0 1 = P.d 0 1 ≫ one)
  (succ : ∀ (n : ℕ) (p : Σ' (f : P.X n ⟶ Q.X n) (f' : P.X (n + 1) ⟶ Q.X (n + 1)),
          f ≫ Q.d n (n + 1) = P.d n (n + 1) ≫ f'),
      Σ' f'' : P.X (n + 2) ⟶ Q.X (n + 2), p.2.1 ≫ Q.d (n + 1) (n + 2) = P.d (n + 1) (n + 2) ≫ f'')

theorem mkHom_f_succ_succ (n : ℕ) :
    (CochainComplex.mkHom P Q HomologicalComplex.zero one one_zero_comm succ).f (n + 2) =
      (succ n
          ⟨(CochainComplex.mkHom P Q HomologicalComplex.zero one one_zero_comm succ).f n,
            (CochainComplex.mkHom P Q HomologicalComplex.zero one one_zero_comm succ).f (n + 1),
            (CochainComplex.mkHom P Q HomologicalComplex.zero one one_zero_comm succ).comm n (n + 1)⟩).1 := by
  dsimp [CochainComplex.mkHom, CochainComplex.mkHomAux]

