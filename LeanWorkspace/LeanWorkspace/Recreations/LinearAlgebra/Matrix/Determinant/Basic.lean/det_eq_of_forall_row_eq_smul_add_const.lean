import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_eq_of_forall_row_eq_smul_add_const {A B : Matrix n n R} (c : n → R) (k : n)
    (hk : c k = 0) (A_eq : ∀ i j, A i j = B i j + c i * B k j) : Matrix.det A = Matrix.det B := Matrix.det_eq_of_forall_row_eq_smul_add_const_aux c
    (fun i =>
      not_imp_comm.mp fun hi =>
        Finset.mem_erase.mpr
          ⟨mt (fun h : i = k => show c i = 0 from h.symm ▸ hk) hi, Finset.mem_univ i⟩)
    k (Finset.notMem_erase k Finset.univ) A_eq

