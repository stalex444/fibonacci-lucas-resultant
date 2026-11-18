module

public import Mathlib
public import SpectralLaw.Lucas

/-!
# SpectralLaw.Law — Theorem 2 (the Fibonacci–Lucas spectral law), for every `n ≥ 3`

The paper (Alexander, doi:10.5281/zenodo.18817597, Theorem 2, transcription :48; overlines
restored from the deposited .docx):

> **Theorem 2 (Fibonacci–Lucas Spectral Law).** For all n ≥ 3, the product polynomial
> P_{2,n}(t) satisfies P_{2,n}(t) mod (t² − t − 1) = (−F_{2n} + (−1)^{n+1}) t − F_{2n−1},
> and the golden-ratio residue norm is N_φ(P_{2,n}) = (−1)^{n+1} L_{2n−1}. Equivalently, as an
> element of ℤ[φ]: P_{2,n}(φ) = −φ^{2n} + (−1)^{n−1} φ.

The paper's Setup (:41) defines `P_{m,n}` as the minimal polynomial of `r_m·r_n`, "computed
via the resultant (2)"; its proof uses only the resultant factorization (6). The kernel
theorems here are about the resultant polynomial `P2 n` (`SpectralLaw.Defs`); they are her
statement wherever `P2 n` is irreducible over `ℚ` (SymPy: `n = 3..20`). Irreducibility of
`P2 n` for general `n` is NOT proved here (named gap).

* `P2_factor` — the paper's (6): `P₂,ₙ = g(φ,t)·g(φ̄,t)` in `ℤ[φ][t]`, `φ̄ = 1 − φ`;
* `P2_root` — `P₂,ₙ(φ·r) = 0` whenever `rⁿ = r + 1`, `φ² = φ + 1`, in any commutative ring;
* `P2_eval_phi` — `P₂,ₙ(φ) = −φ^{2n} + (−1)^{n−1} φ` in `ℤ[φ]`;
* `P2_mod` — the remainder (the paper's (3));
* `P2_goldNorm` — the norm `(−1)^{n+1} L_{2n−1}` (the paper's (4)), as Definition 1 and as
  `Algebra.norm ℤ` on `ℤ[φ]`;
* `P2_natDegree_monic`, `minpoly_dvd_P2`.
-/

@[expose] public section

namespace SpectralLaw

open Polynomial

section Ring

variable {R : Type*} [CommRing R] {φ : R}

/-- The factorization (6) over any commutative ring containing a root `φ` of `t² − t − 1`. -/
lemma map_P2_succ (hφ : φ ^ 2 = φ + 1) (m : ℕ) :
    (P2 (m + 1)).map (algebraMap ℤ R) = gFac (m + 1) φ * gFac (m + 1) (1 - φ) := by
  have hL0 := pow_add_conj_pow hφ m
  have hL1 := pow_add_conj_pow hφ (m + 1)
  simp only [P2, gFac, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, map_X, Polynomial.map_C, Nat.add_sub_cancel]
  simp only [algebraMap_int_eq, eq_intCast, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [← hL0, ← hL1]
  simp only [map_add, map_sub, map_pow, map_neg, map_one]
  have hc : (C φ) ^ 2 = C φ + 1 := by rw [← map_pow, hφ, map_add, map_one]
  have hcd : C φ * (1 - C φ) = -1 := by linear_combination -hc
  have h1 : (C φ) ^ m * (1 - C φ) ^ m = (-1) ^ m := by rw [← mul_pow, hcd]
  linear_combination (1 - X ^ 2 - X) * h1 - (C φ) ^ m * (1 - C φ) ^ m * hcd

lemma eval_gFac_mul {n : ℕ} {r : R} (hn : r ^ (n + 1) = r + 1) :
    eval (φ * r) (gFac (n + 1) φ) = 0 := by
  simp only [gFac, eval_sub, eval_pow, eval_X, eval_mul, eval_C, Nat.add_sub_cancel]
  linear_combination φ ^ (n + 1) * hn

lemma aeval_P2_self (hφ : φ ^ 2 = φ + 1) (m : ℕ) :
    aeval φ (P2 (m + 1)) = -φ ^ (2 * (m + 1)) + (-1) ^ m * φ := by
  rw [aeval_def, ← eval_map, map_P2_succ hφ m, eval_mul]
  simp only [gFac, eval_sub, eval_pow, eval_X, eval_mul, eval_C, Nat.add_sub_cancel]
  have h1 : φ ^ m * (1 - φ) ^ m = (-1) ^ m := by rw [← mul_pow, mul_conj hφ]
  linear_combination φ * h1

end Ring

/-- **The paper's factorization (6).** In `ℤ[φ][t]`,
`P₂,ₙ(t) = g(φ, t)·g(φ̄, t)` with `g(α, t) = tⁿ − α^{n−1} t − αⁿ` and `φ̄ = 1 − φ`. -/
theorem P2_factor (n : ℕ) (hn : 3 ≤ n) :
    (P2 n).map (algebraMap ℤ (AdjoinRoot gZ)) = gFac n phi * gFac n phibar := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact map_P2_succ rootPhi_sq m

/-- **`P₂,ₙ` vanishes at `φ·rₙ`**, in any commutative ring: if `rⁿ = r + 1` and
`φ² = φ + 1` then `P₂,ₙ(φ·r) = 0`. -/
theorem P2_root {R : Type*} [CommRing R] (n : ℕ) (hn : 3 ≤ n) {r φ : R}
    (hr : r ^ n = r + 1) (hφ : φ ^ 2 = φ + 1) : aeval (φ * r) (P2 n) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [aeval_def, ← eval_map, map_P2_succ hφ m, eval_mul,
    eval_gFac_mul hr, zero_mul]

/-- **Theorem 2, the `ℤ[φ]` form:** `P₂,ₙ(φ) = −φ^{2n} + (−1)^{n−1} φ`. -/
theorem P2_eval_phi (n : ℕ) (hn : 3 ≤ n) :
    aeval phi (P2 n) = -phi ^ (2 * n) + (-1) ^ (n - 1) * phi := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact aeval_P2_self rootPhi_sq m

/-- **Theorem 2, the remainder (the paper's (3)):**
`P₂,ₙ(t) mod (t² − t − 1) = (−F_{2n} + (−1)^{n+1}) t − F_{2n−1}`. -/
theorem P2_mod (n : ℕ) (hn : 3 ≤ n) :
    P2 n %ₘ gZ = C (-(Nat.fib (2 * n) : ℤ) + (-1) ^ (n + 1)) * X
      + C (-(Nat.fib (2 * n - 1) : ℤ)) := by
  apply mod_eq_of_mk_eq
  rw [mk_linear, ← AdjoinRoot.aeval_eq, P2_eval_phi n hn]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hp := pow_succ_eq_fib rootPhi_sq (2 * m + 1)
  rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
  simp only [Nat.add_sub_cancel]
  rw [hp]
  push_cast
  ring

/-- The Fibonacci computation in the paper's proof (:62–66): with `a = −F_{2n} + (−1)^{n+1}`
and `b = −F_{2n−1}`, `−a² + ab + b² = (−1)^{n+1} L_{2n−1}` (Cassini plus `L_k = F_{k+1} + F_{k−1}`). -/
theorem fib_norm_identity (n : ℕ) (hn : 1 ≤ n) :
    -(-(Nat.fib (2 * n) : ℤ) + (-1) ^ (n + 1)) ^ 2
      + (-(Nat.fib (2 * n) : ℤ) + (-1) ^ (n + 1)) * (-(Nat.fib (2 * n - 1) : ℤ))
      + (-(Nat.fib (2 * n - 1) : ℤ)) ^ 2 = (-1) ^ (n + 1) * lucas (2 * n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Nat.add_sub_cancel, lucas_succ_eq_fib (2 * m)]
  have hC := cassini (2 * m + 1)
  have hodd : (-1 : ℤ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
  rw [hodd] at hC
  have hF : (Nat.fib (2 * m + 1 + 1) : ℤ) = Nat.fib (2 * m) + Nat.fib (2 * m + 1) := by
    exact_mod_cast Nat.fib_add_two
  have hs : ((-1 : ℤ) ^ (m + 1 + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [show 2 * m + 2 = 2 * m + 1 + 1 by ring]
  linear_combination -hC - hs + (-1 : ℤ) ^ (m + 1 + 1) * hF

/-- **Theorem 2, the norm (the paper's (4)):** `N_φ(P₂,ₙ) = (−1)^{n+1} L_{2n−1}`, both as
Definition 1 (`−a² + ab + b²` of the remainder) and as the field norm of `ℤ[φ]` over `ℤ`. -/
theorem P2_goldNorm (n : ℕ) (hn : 3 ≤ n) :
    goldNorm (P2 n) = (-1) ^ (n + 1) * lucas (2 * n - 1) ∧
      Algebra.norm ℤ (AdjoinRoot.mk gZ (P2 n)) = (-1) ^ (n + 1) * lucas (2 * n - 1) := by
  have h : goldNorm (P2 n) = (-1) ^ (n + 1) * lucas (2 * n - 1) := by
    rw [goldNorm_of_mod (P2_mod n hn)]
    exact fib_norm_identity n (by omega)
  exact ⟨h, by rw [norm_mk_eq_goldNorm, h]⟩

/-- `P₂,ₙ` is monic of degree `2n`. -/
theorem P2_natDegree_monic (n : ℕ) (hn : 3 ≤ n) : (P2 n).natDegree = 2 * n ∧ (P2 n).Monic := by
  have hP : P2 n = X ^ (2 * n) + (-(C (lucas (n - 1)) * X ^ (n + 1)) - C (lucas n) * X ^ n
      + C ((-1 : ℤ) ^ (n - 1)) * X ^ 2 + C ((-1 : ℤ) ^ (n - 1)) * X + C ((-1 : ℤ) ^ n)) := by
    unfold P2; ring
  have hTdeg : (-(C (lucas (n - 1)) * X ^ (n + 1)) - C (lucas n) * X ^ n
      + C ((-1 : ℤ) ^ (n - 1)) * X ^ 2 + C ((-1 : ℤ) ^ (n - 1)) * X
      + C ((-1 : ℤ) ^ n)).natDegree ≤ n + 1 := by
    compute_degree
    omega
  have hlt : (-(C (lucas (n - 1)) * X ^ (n + 1)) - C (lucas n) * X ^ n
      + C ((-1 : ℤ) ^ (n - 1)) * X ^ 2 + C ((-1 : ℤ) ^ (n - 1)) * X
      + C ((-1 : ℤ) ^ n)).degree < ((X : ℤ[X]) ^ (2 * n)).degree := by
    rw [degree_X_pow]
    exact (degree_le_of_natDegree_le hTdeg).trans_lt
      (by exact_mod_cast (show n + 1 < 2 * n by omega))
  rw [hP]
  exact ⟨by rw [natDegree_add_eq_left_of_degree_lt hlt, natDegree_X_pow],
    (monic_X_pow _).add_of_left hlt⟩

/-- The minimal polynomial over `ℚ` of `φ·r` divides `P₂,ₙ`, for any `φ, r` in a field over `ℚ`
with `φ² = φ + 1` and `rⁿ = r + 1` (e.g. the golden ratio and the real root `rₙ`). -/
theorem minpoly_dvd_P2 {K : Type*} [Field K] [Algebra ℚ K] (n : ℕ) (hn : 3 ≤ n) {φ r : K}
    (hφ : φ ^ 2 = φ + 1) (hr : r ^ n = r + 1) :
    minpoly ℚ (φ * r) ∣ (P2 n).map (algebraMap ℤ ℚ) := by
  apply minpoly.dvd
  rw [aeval_map_algebraMap]
  exact P2_root n hn hr hφ

end SpectralLaw
