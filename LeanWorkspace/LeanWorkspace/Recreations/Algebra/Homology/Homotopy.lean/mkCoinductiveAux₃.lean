import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

variable {P Q : CochainComplex V ℕ}

variable (e : P ⟶ Q) (zero : P.X 1 ⟶ Q.X 0) (comm_zero : e.f 0 = P.d 0 1 ≫ zero)
  (one : P.X 2 ⟶ Q.X 1) (comm_one : e.f 1 = zero ≫ Q.d 0 1 + P.d 1 2 ≫ one)
  (succ :
    ∀ (n : ℕ)
      (p :
        Σ' (f : P.X (n + 1) ⟶ Q.X n) (f' : P.X (n + 2) ⟶ Q.X (n + 1)),
          e.f (n + 1) = f ≫ Q.d n (n + 1) + P.d (n + 1) (n + 2) ≫ f'),
      Σ' f'' : P.X (n + 3) ⟶ Q.X (n + 2),
        e.f (n + 2) = p.2.1 ≫ Q.d (n + 1) (n + 2) + P.d (n + 2) (n + 3) ≫ f'')

theorem mkCoinductiveAux₃ (i j : ℕ) (h : i + 1 = j) :
    (P.xNextIso h).inv ≫ (Homotopy.mkCoinductiveAux₂ e zero comm_zero one comm_one succ i).2.1 =
      (Homotopy.mkCoinductiveAux₂ e zero comm_zero one comm_one succ j).1 ≫ (Q.xPrevIso h).hom := by
  subst j
  rcases i with (_ | _ | i) <;> simp [Homotopy.mkCoinductiveAux₂]

