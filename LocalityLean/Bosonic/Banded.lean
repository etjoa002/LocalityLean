/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import LocalityLean.Core.Decay

/-!
# Entrywise bounds on matrix exponentials

The harmonic bound (M5) reduces to the entries of the classical propagator `e^{tK}` of a
quadratic generator `K`. This file proves the general lemma behind it: for a real matrix `K`
over a finite index type, `|(e^{tK})_{ba}| ≤ (e^{|t| |K|})_{ba}` with `|K|` the entrywise
absolute value (M5, Theorem 5.2), and the range and row-sum forms of the right side (M5,
Lemma 5.3 and Corollary 5.4): `(|K|^n)_{ba} = 0` below the distance `n R`, row sums at most
`v^n`, and the tail `(vt)^r/r! e^{vt}` with the light-cone form `e^{-μ r}(e^{e^μ v t} - 1)`.
The matrix `|K|` plays the part of the site matrix of `LocalityLean/Core/SiteMatrix.lean`.

## Main results

* `LocalityLean.Bosonic.absEntry`, `abs_pow_apply_le`, `abs_exp_apply_le`.
* `LocalityLean.Bosonic.HasRange`, `RowSumLE`, `pow_absEntry_apply_eq_zero_of_lt`,
  `sum_pow_absEntry_apply_le`, `exp_absEntry_apply_le_geom`, `exp_absEntry_apply_le_cone`.
-/

namespace LocalityLean.Bosonic

open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The entrywise absolute value of a real matrix (M5, Definition 2.5). -/
def absEntry (K : Matrix ι ι ℝ) : Matrix ι ι ℝ := Matrix.of fun b a => |K b a|

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem absEntry_apply (K : Matrix ι ι ℝ) (b a : ι) : absEntry K b a = |K b a| := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem absEntry_nonneg (K : Matrix ι ι ℝ) (b a : ι) : 0 ≤ absEntry K b a := abs_nonneg _

/-- Entries of powers of `|K|` are nonnegative. -/
theorem pow_absEntry_apply_nonneg (K : Matrix ι ι ℝ) (n : ℕ) (b a : ι) :
    0 ≤ (absEntry K ^ n) b a := by
  induction n generalizing b a with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun c _ => mul_nonneg (ih b c) (absEntry_nonneg K c a)

/-- M5, Lemma 5.1: `|(K^n)_{ba}| ≤ (|K|^n)_{ba}`. -/
theorem abs_pow_apply_le (K : Matrix ι ι ℝ) (n : ℕ) (b a : ι) :
    |(K ^ n) b a| ≤ (absEntry K ^ n) b a := by
  induction n generalizing b a with
  | zero =>
    rw [pow_zero, pow_zero, Matrix.one_apply]
    split_ifs <;> simp
  | succ n ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [abs_mul]
    exact mul_le_mul (ih b c) (le_of_eq rfl) (abs_nonneg _) (pow_absEntry_apply_nonneg K n b c)

set_option backward.isDefEq.respectTransparency false in
/-- The entries of the matrix exponential are the exponential series of the entries of the
powers (the general form of `LocalityLean.LocalGenerators.hasSum_exp_apply`). -/
theorem hasSum_exp_apply (K : Matrix ι ι ℝ) (s : ℝ) (b a : ι) :
    HasSum (fun n : ℕ => s ^ n / (n.factorial : ℝ) * (K ^ n) b a)
      (NormedSpace.exp (s • K) b a) := by
  open scoped Matrix.Norms.Operator in
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (s • K)
  have h2 := Pi.hasSum.1 (Pi.hasSum.1 h b) a
  convert h2 using 1
  funext n
  simp only [Matrix.smul_apply, smul_pow, smul_eq_mul]
  rw [div_eq_inv_mul]
  ring

theorem summable_exp_apply (K : Matrix ι ι ℝ) (s : ℝ) (b a : ι) :
    Summable (fun n : ℕ => s ^ n / (n.factorial : ℝ) * (K ^ n) b a) :=
  (hasSum_exp_apply K s b a).summable

/-- The entries of `e^{t |K|}` are nonnegative for `t ≥ 0`. -/
theorem exp_absEntry_apply_nonneg (K : Matrix ι ι ℝ) {t : ℝ} (ht : 0 ≤ t) (b a : ι) :
    0 ≤ NormedSpace.exp (t • absEntry K) b a :=
  (hasSum_exp_apply (absEntry K) t b a).nonneg fun n =>
    mul_nonneg (div_nonneg (pow_nonneg ht n) (Nat.cast_nonneg _))
      (pow_absEntry_apply_nonneg K n b a)

/-- M5, Theorem 5.2: the entrywise exponential bound
`|(e^{tK})_{ba}| ≤ (e^{|t| |K|})_{ba}`. -/
theorem abs_exp_apply_le (K : Matrix ι ι ℝ) (t : ℝ) (b a : ι) :
    |NormedSpace.exp (t • K) b a| ≤ NormedSpace.exp (|t| • absEntry K) b a := by
  have h1 := hasSum_exp_apply K t b a
  have h2 := hasSum_exp_apply (absEntry K) |t| b a
  have hle : ∀ n : ℕ, |t ^ n / (n.factorial : ℝ) * (K ^ n) b a| ≤
      |t| ^ n / (n.factorial : ℝ) * (absEntry K ^ n) b a := by
    intro n
    rw [abs_mul, abs_div, abs_pow, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left (abs_pow_apply_le K n b a)
      (div_nonneg (pow_nonneg (abs_nonneg t) n) (Nat.cast_nonneg _))
  have hs : Summable fun n : ℕ => |t ^ n / (n.factorial : ℝ) * (K ^ n) b a| :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hle h2.summable
  rw [← h1.tsum_eq, ← h2.tsum_eq]
  calc |∑' n : ℕ, t ^ n / (n.factorial : ℝ) * (K ^ n) b a|
      = ‖∑' n : ℕ, t ^ n / (n.factorial : ℝ) * (K ^ n) b a‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : ℕ, ‖t ^ n / (n.factorial : ℝ) * (K ^ n) b a‖ :=
        norm_tsum_le_tsum_norm (by simpa only [Real.norm_eq_abs] using hs)
    _ = ∑' n : ℕ, |t ^ n / (n.factorial : ℝ) * (K ^ n) b a| := by
        simp only [Real.norm_eq_abs]
    _ ≤ ∑' n : ℕ, |t| ^ n / (n.factorial : ℝ) * (absEntry K ^ n) b a :=
        hs.tsum_le_tsum hle h2.summable

section Range

variable {Λ : Type*}

/-- `K` has range `R` for the distance `d` between the sites of its indices (M5,
Definition 2.5): `K_{ba} = 0` whenever `d(site b, site a) > R`. -/
def HasRange (K : Matrix ι ι ℝ) (site : ι → Λ) (d : Λ → Λ → ℝ) (R : ℝ) : Prop :=
  ∀ b a, R < d (site b) (site a) → K b a = 0

/-- `K` has row sum at most `v` (M5, Definition 2.5): `∑_a |K_{ba}| ≤ v` for every `b`. -/
def RowSumLE (K : Matrix ι ι ℝ) (v : ℝ) : Prop :=
  ∀ b, ∑ a, |K b a| ≤ v

/-- M5, Lemma 5.3 (vanishing): `(|K|^n)_{ba} = 0` when `n R < d(site b, site a)`, for a
distance with `d x x = 0` and the triangle inequality. -/
theorem pow_absEntry_apply_eq_zero_of_lt {K : Matrix ι ι ℝ} {site : ι → Λ} {d : Λ → Λ → ℝ}
    {R : ℝ} (hd0 : ∀ x, d x x = 0) (hd : ∀ x y z, d x z ≤ d x y + d y z)
    (hR : HasRange K site d R) (n : ℕ) {b a : ι}
    (h : (n : ℝ) * R < d (site b) (site a)) : (absEntry K ^ n) b a = 0 := by
  induction n generalizing a with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    rw [Nat.cast_zero, zero_mul] at h
    have hba : b ≠ a := by
      rintro rfl
      rw [hd0] at h
      exact lt_irrefl _ h
    exact ite_eq_right hba
  | succ n ih =>
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hca : R < d (site c) (site a)
    · rw [absEntry_apply, hR c a hca, abs_zero, mul_zero]
    · have hca' : d (site c) (site a) ≤ R := not_lt.1 hca
      have hbc : (n : ℝ) * R < d (site b) (site c) := by
        have := hd (site b) (site c) (site a)
        push_cast at h
        linarith
      rw [ih (a := c) hbc, zero_mul]

/-- M5, Lemma 5.3 (row sums): `∑_a (|K|^n)_{ba} ≤ v^n`. -/
theorem sum_pow_absEntry_apply_le {K : Matrix ι ι ℝ} {v : ℝ} (hv : RowSumLE K v) (hv0 : 0 ≤ v)
    (n : ℕ) (b : ι) : ∑ a, (absEntry K ^ n) b a ≤ v ^ n := by
  induction n generalizing b with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true, le_refl]
  | succ n ih =>
    calc ∑ a, (absEntry K ^ (n + 1)) b a
        = ∑ c, absEntry K b c * ∑ a, (absEntry K ^ n) c a := by
          simp only [pow_succ', Matrix.mul_apply, Finset.mul_sum]
          exact Finset.sum_comm
      _ ≤ ∑ c, absEntry K b c * v ^ n :=
          Finset.sum_le_sum fun c _ =>
            mul_le_mul_of_nonneg_left (ih c) (absEntry_nonneg K b c)
      _ = (∑ c, |K b c|) * v ^ n := by rw [Finset.sum_mul]; rfl
      _ ≤ v * v ^ n := mul_le_mul_of_nonneg_right (hv b) (pow_nonneg hv0 n)
      _ = v ^ (n + 1) := (pow_succ' v n).symm

/-- One entry is at most the row sum. -/
theorem pow_absEntry_apply_le_sum (K : Matrix ι ι ℝ) (n : ℕ) (b a : ι) :
    (absEntry K ^ n) b a ≤ ∑ a', (absEntry K ^ n) b a' :=
  Finset.single_le_sum (fun a' _ => pow_absEntry_apply_nonneg K n b a') (Finset.mem_univ a)

/-- M5, Corollary 5.4 (range form): if `n R < d(site b, site a)` for every `n < r`, then
`(e^{t |K|})_{ba} ≤ (vt)^r/r! e^{vt}` for `t ≥ 0`. -/
theorem exp_absEntry_apply_le_geom {K : Matrix ι ι ℝ} {site : ι → Λ} {d : Λ → Λ → ℝ}
    {R v : ℝ} (hd0 : ∀ x, d x x = 0) (hd : ∀ x y z, d x z ≤ d x y + d y z)
    (hR : HasRange K site d R) (hv : RowSumLE K v) (hv0 : 0 ≤ v)
    {t : ℝ} (ht : 0 ≤ t) {r : ℕ} {b a : ι} (hr : ∀ n < r, n * R < d (site b) (site a)) :
    NormedSpace.exp (t • absEntry K) b a ≤
      (v * t) ^ r / (r.factorial : ℝ) * Real.exp (v * t) := by
  have hs := hasSum_exp_apply (absEntry K) t b a
  rw [← hs.tsum_eq, ← hs.summable.sum_add_tsum_nat_add r]
  have hzero : ∑ i ∈ Finset.range r, t ^ i / (i.factorial : ℝ) * (absEntry K ^ i) b a = 0 :=
    Finset.sum_eq_zero fun n hn => by
      rw [pow_absEntry_apply_eq_zero_of_lt hd0 hd hR n (hr n (Finset.mem_range.1 hn)), mul_zero]
  rw [hzero, zero_add]
  have hle : ∀ j : ℕ, t ^ (j + r) / ((j + r).factorial : ℝ) * (absEntry K ^ (j + r)) b a ≤
      (v * t) ^ (j + r) / ((j + r).factorial : ℝ) := by
    intro j
    calc t ^ (j + r) / ((j + r).factorial : ℝ) * (absEntry K ^ (j + r)) b a
        ≤ t ^ (j + r) / ((j + r).factorial : ℝ) * v ^ (j + r) :=
          mul_le_mul_of_nonneg_left
            ((pow_absEntry_apply_le_sum K _ b a).trans (sum_pow_absEntry_apply_le hv hv0 _ b))
            (div_nonneg (pow_nonneg ht _) (Nat.cast_nonneg _))
      _ = (v * t) ^ (j + r) / ((j + r).factorial : ℝ) := by rw [mul_pow]; ring
  have hsum : Summable fun j : ℕ => (v * t) ^ (j + r) / ((j + r).factorial : ℝ) :=
    (summable_nat_add_iff r).2 (Real.summable_pow_div_factorial (v * t))
  calc ∑' j : ℕ, t ^ (j + r) / ((j + r).factorial : ℝ) * (absEntry K ^ (j + r)) b a
      ≤ ∑' j : ℕ, (v * t) ^ (j + r) / ((j + r).factorial : ℝ) :=
        ((summable_nat_add_iff r).2 hs.summable).tsum_le_tsum hle hsum
    _ ≤ (v * t) ^ r / (r.factorial : ℝ) * Real.exp (v * t) :=
        tsum_pow_div_factorial_tail_le (mul_nonneg hv0 ht) r

/-- M5, Corollary 5.4 (light cone): for `μ ≥ 0` and `r ≥ 1`,
`(e^{t |K|})_{ba} ≤ e^{-μ r} (e^{e^μ v t} - 1)` under the hypotheses of the range form. -/
theorem exp_absEntry_apply_le_cone {K : Matrix ι ι ℝ} {site : ι → Λ} {d : Λ → Λ → ℝ}
    {R v : ℝ} (hd0 : ∀ x, d x x = 0) (hd : ∀ x y z, d x z ≤ d x y + d y z)
    (hR : HasRange K site d R) (hv : RowSumLE K v) (hv0 : 0 ≤ v)
    {t : ℝ} (ht : 0 ≤ t) {μ : ℝ} (hμ : 0 ≤ μ) {r : ℕ} (hr1 : 1 ≤ r) {b a : ι}
    (hr : ∀ n < r, n * R < d (site b) (site a)) :
    NormedSpace.exp (t • absEntry K) b a ≤
      Real.exp (-μ * r) * (Real.exp (Real.exp μ * (v * t)) - 1) := by
  have hs := hasSum_exp_apply (absEntry K) t b a
  rw [← hs.tsum_eq, ← hs.summable.sum_add_tsum_nat_add r]
  have hzero : ∑ i ∈ Finset.range r, t ^ i / (i.factorial : ℝ) * (absEntry K ^ i) b a = 0 :=
    Finset.sum_eq_zero fun n hn => by
      rw [pow_absEntry_apply_eq_zero_of_lt hd0 hd hR n (hr n (Finset.mem_range.1 hn)), mul_zero]
  rw [hzero, zero_add]
  have hvt : 0 ≤ v * t := mul_nonneg hv0 ht
  have hy : 0 ≤ Real.exp μ * (v * t) := mul_nonneg (Real.exp_pos μ).le hvt
  have hle : ∀ j : ℕ, t ^ (j + r) / ((j + r).factorial : ℝ) * (absEntry K ^ (j + r)) b a ≤
      (v * t) ^ (j + r) / ((j + r).factorial : ℝ) := by
    intro j
    calc t ^ (j + r) / ((j + r).factorial : ℝ) * (absEntry K ^ (j + r)) b a
        ≤ t ^ (j + r) / ((j + r).factorial : ℝ) * v ^ (j + r) :=
          mul_le_mul_of_nonneg_left
            ((pow_absEntry_apply_le_sum K _ b a).trans (sum_pow_absEntry_apply_le hv hv0 _ b))
            (div_nonneg (pow_nonneg ht _) (Nat.cast_nonneg _))
      _ = (v * t) ^ (j + r) / ((j + r).factorial : ℝ) := by rw [mul_pow]; ring
  have hle2 : ∀ j : ℕ, (v * t) ^ (j + r) / ((j + r).factorial : ℝ) ≤
      Real.exp (-μ * r) *
        ((Real.exp μ * (v * t)) ^ (j + r) / ((j + r).factorial : ℝ)) := by
    intro j
    have h1 : 1 ≤ Real.exp (-μ * r) * Real.exp μ ^ (j + r) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      refine Real.one_le_exp ?_
      push_cast
      nlinarith [mul_nonneg hμ (Nat.cast_nonneg (α := ℝ) j)]
    have h2 : 0 ≤ (v * t) ^ (j + r) / ((j + r).factorial : ℝ) :=
      div_nonneg (pow_nonneg hvt _) (Nat.cast_nonneg _)
    calc (v * t) ^ (j + r) / ((j + r).factorial : ℝ)
        = 1 * ((v * t) ^ (j + r) / ((j + r).factorial : ℝ)) := (one_mul _).symm
      _ ≤ Real.exp (-μ * r) * Real.exp μ ^ (j + r) *
            ((v * t) ^ (j + r) / ((j + r).factorial : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = Real.exp (-μ * r) *
            ((Real.exp μ * (v * t)) ^ (j + r) / ((j + r).factorial : ℝ)) := by
          rw [mul_pow]; ring
  have hsum : Summable fun j : ℕ => (v * t) ^ (j + r) / ((j + r).factorial : ℝ) :=
    (summable_nat_add_iff r).2 (Real.summable_pow_div_factorial (v * t))
  have hsumy : Summable fun j : ℕ =>
      (Real.exp μ * (v * t)) ^ (j + r) / ((j + r).factorial : ℝ) :=
    (summable_nat_add_iff r).2 (Real.summable_pow_div_factorial (Real.exp μ * (v * t)))
  have htail : ∑' j : ℕ, (Real.exp μ * (v * t)) ^ (j + r) / ((j + r).factorial : ℝ) ≤
      Real.exp (Real.exp μ * (v * t)) - 1 := by
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    have hg := (summable_nat_add_iff 1).2
      (Real.summable_pow_div_factorial (Real.exp μ * (v * t)))
    rw [← tsum_pow_succ_div_factorial, ← hg.sum_add_tsum_nat_add m]
    have hnn : 0 ≤ ∑ i ∈ Finset.range m,
        (Real.exp μ * (v * t)) ^ (i + 1) / ((i + 1).factorial : ℝ) :=
      Finset.sum_nonneg fun i _ => div_nonneg (pow_nonneg hy _) (Nat.cast_nonneg _)
    simp only [add_assoc] at hnn ⊢
    linarith
  calc ∑' j : ℕ, t ^ (j + r) / ((j + r).factorial : ℝ) * (absEntry K ^ (j + r)) b a
      ≤ ∑' j : ℕ, (v * t) ^ (j + r) / ((j + r).factorial : ℝ) :=
        ((summable_nat_add_iff r).2 hs.summable).tsum_le_tsum hle hsum
    _ ≤ ∑' j : ℕ, Real.exp (-μ * r) *
          ((Real.exp μ * (v * t)) ^ (j + r) / ((j + r).factorial : ℝ)) :=
        hsum.tsum_le_tsum hle2 (hsumy.mul_left _)
    _ = Real.exp (-μ * r) *
          ∑' j : ℕ, (Real.exp μ * (v * t)) ^ (j + r) / ((j + r).factorial : ℝ) := tsum_mul_left
    _ ≤ Real.exp (-μ * r) * (Real.exp (Real.exp μ * (v * t)) - 1) :=
        mul_le_mul_of_nonneg_left htail (Real.exp_pos _).le

end Range

end LocalityLean.Bosonic
