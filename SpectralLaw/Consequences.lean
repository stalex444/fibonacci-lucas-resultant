module

public import Mathlib
public import SpectralLaw.Law

/-!
# SpectralLaw.Consequences — consequences of Theorem 2 along the `m = 2` row

The signed Lucas norm gives a sharp lower bound on its absolute value. Equality holds precisely at n = 3. The remaining lemmas give consequences for units and growth along the same row.
-/

@[expose] public section

namespace SpectralLaw

open Polynomial Filter

/-- `|N_φ(P₂,ₙ)| = L_{2n−1}`. -/
theorem P2_abs_goldNorm (n : ℕ) (hn : 3 ≤ n) : |goldNorm (P2 n)| = lucas (2 * n - 1) := by
  rw [(P2_goldNorm n hn).1, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (by linarith [(lucas_ge (2 * n - 1)).2])]

/-- `|N_φ(P₂,ₙ)| ≥ 11 = L₅` for every `n ≥ 3`. -/
theorem P2_goldNorm_ge (n : ℕ) (hn : 3 ≤ n) : 11 ≤ |goldNorm (P2 n)| := by
  rw [P2_abs_goldNorm n hn]
  have h : lucas (4 + 1) ≤ lucas (2 * n - 2 + 1) := lucas_strictMono.monotone (by omega)
  rw [show 2 * n - 2 + 1 = 2 * n - 1 by omega] at h
  have h5 : lucas (4 + 1) = 11 := by decide
  linarith

/-- The minimum `|N_φ(P₂,ₙ)| = 11` is attained exactly at `n = 3`. -/
theorem P2_goldNorm_eq_eleven_iff (n : ℕ) (hn : 3 ≤ n) : |goldNorm (P2 n)| = 11 ↔ n = 3 := by
  rw [P2_abs_goldNorm n hn]
  constructor
  · intro h
    have h5 : lucas (4 + 1) = 11 := by decide
    have h' : lucas (2 * n - 2 + 1) = lucas (4 + 1) := by
      rw [show 2 * n - 2 + 1 = 2 * n - 1 by omega, h, h5]
    have := lucas_strictMono.injective h'
    omega
  · rintro rfl
    decide

/-- On the `m = 2` row the golden residue norm is never `±1`. -/
theorem P2_goldNorm_ne_unit (n : ℕ) (hn : 3 ≤ n) :
    goldNorm (P2 n) ≠ 1 ∧ goldNorm (P2 n) ≠ -1 := by
  have h := P2_goldNorm_ge n hn
  constructor
  · intro h'
    rw [h'] at h
    norm_num at h
  · intro h'
    rw [h'] at h
    norm_num at h

/-- On the `m = 2` row the image of `P₂,ₙ` in `ℤ[φ]` is never a unit. -/
theorem P2_residue_not_isUnit (n : ℕ) (hn : 3 ≤ n) : ¬ IsUnit (AdjoinRoot.mk gZ (P2 n)) := by
  intro hu
  have h := hu.map (Algebra.norm ℤ)
  rw [norm_mk_eq_goldNorm] at h
  rcases Int.isUnit_iff.1 h with h' | h'
  · exact (P2_goldNorm_ne_unit n hn).1 h'
  · exact (P2_goldNorm_ne_unit n hn).2 h'

/-- `|N_φ(P₂,ₙ)| → ∞`: divergence only; the paper's Remark 1 also gives the rate `C·φ^{2n}`, not proved here. -/
theorem P2_goldNorm_tendsto : Tendsto (fun n => |goldNorm (P2 n)|) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 3] with n hn
  rw [P2_abs_goldNorm n hn]
  have h1 := (lucas_ge (2 * n - 1)).1
  have h2 : (n : ℤ) ≤ ((2 * n - 1 : ℕ) : ℤ) := by exact_mod_cast (by omega : n ≤ 2 * n - 1)
  linarith

end SpectralLaw
