import Mathlib

variable {K R L M : Type*}

variable [Field K] [CommRing R]

variable [LieRing L] [LieAlgebra K L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [Module.Finite K L]

variable [Module.Finite R L] [Module.Free R L]

variable [Module.Finite R M] [Module.Free R M]

variable (x y : L)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem lieCharpoly_map_eval (r : R) :
    (LieAlgebra.engel_isBot_of_isMin.lieCharpoly R M x y).map (evalRingHom r) = (φ (r • y + x)).charpoly := by
  rw [LieAlgebra.engel_isBot_of_isMin.lieCharpoly, map_map]
  set b := chooseBasis R L
  have aux : (fun i ↦ (b.repr y) i * r + (b.repr x) i) = b.repr (r • y + x) := by
    ext i; simp [mul_comm r]
  simp_rw [← coe_aeval_eq_evalRingHom, ← AlgHom.comp_toRingHom, MvPolynomial.comp_aeval,
    map_add, map_mul, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, aeval_X, aux,
    MvPolynomial.coe_aeval_eq_eval, polyCharpoly_map_eq_charpoly, LieHom.coe_toLinearMap, map_add]

