module

public import Mathlib
public import SpectralLaw.Defs

/-!
# SpectralLaw.Basic — `ℤ[φ] = ℤ[t]/(t² − t − 1)`, and Definition 1 is its field norm

The quadratic norm of a linear residue a·φ + b is −a² + ab + b².
The norm and residue lemmas were ported from Stephanie Alexander’s earlier
`PdtGoldenResidue.lean` (revision `813b46e265560ff397e365cbd8486e603298a96d`).
-/

@[expose] public section

namespace SpectralLaw

open Polynomial

lemma gZ_monic : gZ.Monic := by unfold gZ; monicity!

lemma gZ_natDegree : gZ.natDegree = 2 := by unfold gZ; compute_degree!

lemma gZ_degree : gZ.degree = 2 := by unfold gZ; compute_degree!

lemma gZ_ne_one : gZ ≠ 1 := by
  intro h
  have h2 := gZ_natDegree
  rw [h, natDegree_one] at h2
  omega

lemma goldNorm_of_mod {F : ℤ[X]} {a b : ℤ} (h : F %ₘ gZ = C a * X + C b) :
    goldNorm F = -a ^ 2 + a * b + b ^ 2 := by
  unfold goldNorm
  rw [h]
  simp only [coeff_add, coeff_C_mul_X, coeff_C]
  simp

lemma dim_two : (AdjoinRoot.powerBasis' gZ_monic).dim = 2 := by
  rw [AdjoinRoot.powerBasis'_dim, gZ_natDegree]

/-- The power basis `1, φ` of `ℤ[φ]`, indexed by `Fin 2`. -/
noncomputable def bPhi :=
  (AdjoinRoot.powerBasis' gZ_monic).basis.reindex (finCongr dim_two)

lemma bPhi_apply (j : Fin 2) : bPhi j = AdjoinRoot.root gZ ^ (j : ℕ) := by
  rw [bPhi, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, AdjoinRoot.powerBasis'_gen]
  rfl

lemma bPhi_repr (p : ℤ[X]) (i : Fin 2) :
    bPhi.repr (AdjoinRoot.mk gZ p) i = (p %ₘ gZ).coeff (i : ℕ) := by
  rw [bPhi, Module.Basis.repr_reindex_apply]
  refine (AdjoinRoot.powerBasisAux'_repr_apply_to_fun gZ_monic (AdjoinRoot.mk gZ p)
    ((finCongr dim_two).symm i)).trans ?_
  rw [AdjoinRoot.modByMonicHom_mk]
  rfl

lemma leftMul_entry (p : ℤ[X]) (i j : Fin 2) :
    Algebra.leftMulMatrix bPhi (AdjoinRoot.mk gZ p) i j
      = ((p * X ^ (j : ℕ)) %ₘ gZ).coeff (i : ℕ) := by
  rw [Algebra.leftMulMatrix_eq_repr_mul, bPhi_apply, ← AdjoinRoot.mk_X, ← map_pow, ← map_mul,
    bPhi_repr]

lemma mod_linear (a b : ℤ) : (C a * X + C b) %ₘ gZ = C a * X + C b :=
  (modByMonic_eq_self_iff gZ_monic).2 (by rw [gZ_degree]; exact degree_linear_lt)

lemma mod_linear_mul_X (a b : ℤ) : ((C a * X + C b) * X) %ₘ gZ = C (a + b) * X + C a :=
  (div_modByMonic_unique (f := (C a * X + C b) * X) (C a) (C (a + b) * X + C a) gZ_monic
    ⟨by unfold gZ; rw [C_add]; ring, by rw [gZ_degree]; exact degree_linear_lt⟩).2

/-- The norm of `a·φ + b` in `ℤ[φ]` is `−a² + ab + b²`. -/
theorem norm_linear (a b : ℤ) :
    Algebra.norm ℤ (AdjoinRoot.mk gZ (C a * X + C b)) = -a ^ 2 + a * b + b ^ 2 := by
  have e00 : Algebra.leftMulMatrix bPhi (AdjoinRoot.mk gZ (C a * X + C b)) 0 0 = b := by
    rw [leftMul_entry, Fin.val_zero, pow_zero, mul_one, mod_linear]
    simp only [coeff_add, coeff_C_mul_X, coeff_C]
    simp
  have e10 : Algebra.leftMulMatrix bPhi (AdjoinRoot.mk gZ (C a * X + C b)) 1 0 = a := by
    rw [leftMul_entry, Fin.val_zero, pow_zero, mul_one, mod_linear]
    simp only [coeff_add, coeff_C_mul_X, coeff_C]
    simp
  have e01 : Algebra.leftMulMatrix bPhi (AdjoinRoot.mk gZ (C a * X + C b)) 0 1 = a := by
    rw [leftMul_entry, Fin.val_one, pow_one, mod_linear_mul_X]
    simp only [coeff_add, coeff_C_mul_X, coeff_C]
    simp
  have e11 : Algebra.leftMulMatrix bPhi (AdjoinRoot.mk gZ (C a * X + C b)) 1 1 = a + b := by
    rw [leftMul_entry, Fin.val_one, pow_one, mod_linear_mul_X]
    simp only [coeff_add, coeff_C_mul_X, coeff_C]
    simp
  rw [Algebra.norm_eq_matrix_det bPhi, Matrix.det_fin_two, e00, e01, e10, e11]
  ring

lemma mk_eq_mk_mod (F : ℤ[X]) : AdjoinRoot.mk gZ F = AdjoinRoot.mk gZ (F %ₘ gZ) := by
  rw [AdjoinRoot.mk_eq_mk]
  exact ⟨F /ₘ gZ, by linear_combination -(modByMonic_add_div F gZ)⟩

/-- **Definition 1 is the field norm.** For every `F ∈ ℤ[t]`, the golden residue norm of
`F` is the norm, from `ℤ[φ]` down to `ℤ`, of the image of `F` in `ℤ[φ]`. -/
theorem norm_mk_eq_goldNorm (F : ℤ[X]) :
    Algebra.norm ℤ (AdjoinRoot.mk gZ F) = goldNorm F := by
  have hdeg : (F %ₘ gZ).natDegree ≤ 1 := by
    have h := natDegree_modByMonic_lt F gZ_monic gZ_ne_one
    rw [gZ_natDegree] at h
    omega
  rw [mk_eq_mk_mod F, eq_X_add_C_of_natDegree_le_one hdeg, norm_linear]
  rfl

/-- In `ℤ[φ]`, `φ² = φ + 1`. -/
lemma rootPhi_sq : phi ^ 2 = phi + 1 := by
  have h : (aeval (AdjoinRoot.root gZ)) gZ = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have h2 : (AdjoinRoot.root gZ) ^ 2 - AdjoinRoot.root gZ - 1 = 0 := by
    have : (aeval (AdjoinRoot.root gZ)) gZ
        = (AdjoinRoot.root gZ) ^ 2 - AdjoinRoot.root gZ - 1 := by
      unfold gZ; simp [map_sub, map_pow]
    rw [← this]; exact h
  linear_combination h2

/-- The image of `a·t + b` in `ℤ[φ]` is `a·φ + b`. -/
lemma mk_linear (a b : ℤ) :
    AdjoinRoot.mk gZ (C a * X + C b) = (a : AdjoinRoot gZ) * phi + (b : AdjoinRoot gZ) := by
  rw [map_add, map_mul, AdjoinRoot.mk_X, eq_intCast C a, eq_intCast C b, map_intCast,
    map_intCast]

/-- Remainder uniqueness through `ℤ[φ]`: if `F` and `a·t + b` have the same image in `ℤ[φ]`,
then `F %ₘ (t² − t − 1) = a·t + b`. -/
lemma mod_eq_of_mk_eq {F : ℤ[X]} {a b : ℤ}
    (h : AdjoinRoot.mk gZ F = AdjoinRoot.mk gZ (C a * X + C b)) :
    F %ₘ gZ = C a * X + C b := by
  rw [AdjoinRoot.mk_eq_mk] at h
  obtain ⟨q, hq⟩ := h
  exact (div_modByMonic_unique (f := F) q (C a * X + C b) gZ_monic
    ⟨by linear_combination -hq, by rw [gZ_degree]; exact degree_linear_lt⟩).2

end SpectralLaw
