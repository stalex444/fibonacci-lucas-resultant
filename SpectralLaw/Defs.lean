module

public import Mathlib

/-!
# SpectralLaw.Defs — the objects of Theorem 2 of the Fibonacci–Lucas spectral law

Source: S. Alexander, *A Fibonacci–Lucas Spectral Law for the Trinomials xⁿ = x + 1*,
Zenodo, doi:10.5281/zenodo.18817597 (2026-02-28).

* `gZ` — the golden polynomial `t² − t − 1` over `ℤ` (the paper's modulus, `= f₂`).
* `goldNorm` — the paper's Definition 1: `N_φ(F) = −a² + ab + b²` where
  `F mod (t² − t − 1) = a·t + b`.
* `lucas` — the Lucas numbers, by their recurrence (`L₀ = 2`, `L₁ = 1`).
* `P2 n` — the integer polynomial
  `t^{2n} − L_{n−1} t^{n+1} − L_n tⁿ + (−1)^{n−1} t² + (−1)^{n−1} t + (−1)ⁿ`.
  It is the resultant of the paper's eq. (2) with `m = 2`,
  `Res_x(x² − x − 1, tⁿ − t x^{n−1} − xⁿ)`: see `SpectralLaw.P2_factor` (the paper's (6))
  and `SpectralLaw.P2_eq_resultant` (against Mathlib's `Polynomial.resultant`).
* `gFac n α = tⁿ − α^{n−1} t − αⁿ` — the paper's `g(α, t)`.
* `phi`, `phibar` — the root `φ` of `gZ` in `ℤ[φ] = AdjoinRoot gZ` and its conjugate
  `φ̄ = 1 − φ`.
-/

@[expose] public section

namespace SpectralLaw

open Polynomial

/-- The golden polynomial `t² − t − 1` over `ℤ`. -/
noncomputable def gZ : ℤ[X] := X ^ 2 - X - 1

/-- **Definition 1** (golden-ratio residue norm): `N_φ(F) = −a² + ab + b²` where
`F mod (t² − t − 1) = a·t + b`. -/
noncomputable def goldNorm (F : ℤ[X]) : ℤ :=
  -((F %ₘ gZ).coeff 1) ^ 2 + (F %ₘ gZ).coeff 1 * (F %ₘ gZ).coeff 0 + ((F %ₘ gZ).coeff 0) ^ 2

/-- The Lucas numbers `L₀ = 2`, `L₁ = 1`, `L_{k+2} = L_k + L_{k+1}`. -/
def lucas : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | k + 2 => lucas k + lucas (k + 1)

/-- The product polynomial `P₂,ₙ` of the paper's eq. (2) (`m = 2`), in closed form:
`t^{2n} − L_{n−1} t^{n+1} − L_n tⁿ + (−1)^{n−1} t² + (−1)^{n−1} t + (−1)ⁿ`. -/
noncomputable def P2 (n : ℕ) : ℤ[X] :=
  X ^ (2 * n) - C (lucas (n - 1)) * X ^ (n + 1) - C (lucas n) * X ^ n
    + C ((-1 : ℤ) ^ (n - 1)) * X ^ 2 + C ((-1 : ℤ) ^ (n - 1)) * X + C ((-1 : ℤ) ^ n)

/-- The paper's `g(α, t) = tⁿ − α^{n−1} t − αⁿ`. -/
noncomputable def gFac {R : Type*} [CommRing R] (n : ℕ) (α : R) : R[X] :=
  X ^ n - C (α ^ (n - 1)) * X - C (α ^ n)

/-- `φ`, the root of `t² − t − 1` in `ℤ[φ] = AdjoinRoot gZ`. -/
noncomputable abbrev phi : AdjoinRoot gZ := AdjoinRoot.root gZ

/-- `φ̄ = 1 − φ`, the Galois conjugate of `φ` in `ℤ[φ]`. -/
noncomputable abbrev phibar : AdjoinRoot gZ := 1 - AdjoinRoot.root gZ

end SpectralLaw
