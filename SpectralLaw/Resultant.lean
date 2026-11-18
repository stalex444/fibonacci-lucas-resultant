module

public import Mathlib
public import SpectralLaw.Law

/-!
# SpectralLaw.Resultant — `P2 n` IS the resultant of the paper's eq. (2) with `m = 2`

The paper (:41–43) computes `P_{m,n}(t) = Res_x(x^m − x − 1, tⁿ − t x^{n−1} − xⁿ)`. Here, against
Mathlib's `Polynomial.resultant` (Sylvester determinant, default sizes the natural degrees),
for `m = 2` and every `n ≥ 3`:
`resultant (x² − x − 1) (tⁿ − t x^{n−1} − xⁿ) = P2 n` in `ℤ[t]`.

Route: map `ℤ[t] → ℝ[t]` (injective), split `x² − x − 1 = (x − φ)(x − (1 − φ))` with `φ` the
golden ratio, `resultant_mul_left` and `resultant_X_sub_C_left`, then the factorization (6).
-/

@[expose] public section

namespace SpectralLaw

open Polynomial

/-- `tⁿ − t x^{n−1} − xⁿ` as a polynomial in `x` over `ℤ[t]`: the second argument of eq. (2). -/
noncomputable def resG (n : ℕ) : ℤ[X][X] := C (X ^ n) - C X * X ^ (n - 1) - X ^ n

lemma natDegree_golden_xx : (X ^ 2 - X - 1 : ℤ[X][X]).natDegree = 2 := by compute_degree!

lemma natDegree_resG (n : ℕ) (hn : 1 ≤ n) : (resG n).natDegree = n := by
  have hle : (resG n).natDegree ≤ n := by
    unfold resG
    compute_degree
  refine natDegree_eq_of_le_of_coeff_ne_zero hle ?_
  have h1 : n ≠ n - 1 := by omega
  have h0 : n ≠ 0 := by omega
  rw [resG, coeff_sub, coeff_sub, coeff_C, coeff_C_mul_X_pow, coeff_X_pow_self]
  simp [h0, h1]

/-- **The resultant tie (the paper's eq. (2), `m = 2`).** For every `n ≥ 3`,
`Res_x(x² − x − 1, tⁿ − t x^{n−1} − xⁿ) = P₂,ₙ(t)` in `ℤ[t]`. -/
theorem P2_eq_resultant (n : ℕ) (hn : 3 ≤ n) :
    resultant (X ^ 2 - X - 1 : ℤ[X][X]) (resG n) = P2 n := by
  set ι : ℤ[X] →+* ℝ[X] := mapRingHom (Int.castRingHom ℝ) with hι
  have hinj : Function.Injective ι := Polynomial.map_injective _ Int.cast_injective
  apply hinj
  rw [natDegree_golden_xx, natDegree_resG n (by omega), ← resultant_map_map _ _ _ _ ι]
  have hφ : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  have hc : (C (C Real.goldenRatio) : ℝ[X][X]) ^ 2 = C (C Real.goldenRatio) + 1 := by
    rw [← map_pow, ← map_pow, hφ, map_add, map_add, map_one, map_one]
  have hf : (X ^ 2 - X - 1 : ℤ[X][X]).map ι
      = (X - C (C Real.goldenRatio)) * (X - C (C (1 - Real.goldenRatio))) := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one, map_sub,
      map_one]
    linear_combination hc
  have hg : (resG n).map ι = C (X ^ n) - C X * X ^ (n - 1) - X ^ n := by
    simp [resG, hι]
  have hgdeg : ((resG n).map ι).natDegree ≤ n :=
    natDegree_map_le.trans (natDegree_resG n (by omega)).le
  have hmul := resultant_mul_left (X - C (C Real.goldenRatio))
    (X - C (C (1 - Real.goldenRatio))) ((resG n).map ι) n hgdeg
  rw [natDegree_X_sub_C, natDegree_X_sub_C, resultant_X_sub_C_left _ _ _ hgdeg,
    resultant_X_sub_C_left _ _ _ hgdeg] at hmul
  rw [hf]
  refine hmul.trans ?_
  have hP : ι (P2 n) = (P2 n).map (algebraMap ℤ ℝ) := by
    rw [hι, coe_mapRingHom, algebraMap_int_eq]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [hP, map_P2_succ hφ m, hg]
  simp only [gFac, eval_sub, eval_mul, eval_pow, eval_C, eval_X, Nat.add_sub_cancel, map_pow]
  ring

end SpectralLaw
