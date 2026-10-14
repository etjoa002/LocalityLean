/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import LocalityLean.Core.SiteMatrix
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Decay kernels and the geometric forms (M1b, closed forms (ii)-(iv))

A decay kernel is a nonnegative function `F` on pairs of sites with a reproducing constant
`C_F > 0`, `Σ_{z ∈ T'} F(x, z) F(z, y) ≤ C_F F(x, y)` for every finite `T'` (M1b,
Definition 2.4); an `F`-bound of the family is a constant `N_F` with `h_{xy} ≤ N_F F(x, y)`.
The walk weights are then bounded by `N_F^k C_F^{k-1} F(y, x)` (Proposition 3.7), which gives the
decay-function form of the bound (Theorem 3.8).

With bounded geometry (a distance with the triangle inequality, at most `g` terms per site,
strengths at most `ℓ`, supports of at most `R` sites and diameter at most `ρ`; Definition 2.5),
the walks of `k` steps vanish beyond distance `kρ` (Proposition 4.1) and the bound takes the form
`(vt)^r e^{vt}/r!` with `v = 2gℓR` (Theorem 4.2), hence an exponential light cone (Theorem 4.4).

## Main definitions

* `LocalityLean.DecayKernel`, `LocalityLean.LocalGenerators.IsFBound`.
* `LocalityLean.LocalGenerators.BoundedGeometry`.

## Main statements

* `LocalityLean.LocalGenerators.walk_le_decay`, `liebRobinson_decay` (Theorem 3.8).
* `LocalityLean.tsum_pow_div_factorial_tail_le` (Lemma 3.9), `pow_div_factorial_le_exp_sub`
  (Lemma 4.3).
* `LocalityLean.LocalGenerators.liebRobinson_boundedGeometry` (Theorem 4.2),
  `liebRobinson_cone` (Theorem 4.4).
-/

noncomputable section

namespace LocalityLean

open LinearAQFT Finset

/-! ### Facts about the exponential series -/

/-- The real exponential as its series, `e^x = Σ_n x^n/n!`. -/
theorem Real.exp_eq_tsum_pow_div_factorial (x : ℝ) :
    Real.exp x = ∑' n : ℕ, x ^ n / (n.factorial : ℝ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- `Σ_{k ≥ 0} x^{k+1}/(k+1)! = e^x - 1`. -/
theorem tsum_pow_succ_div_factorial (x : ℝ) :
    ∑' k : ℕ, x ^ (k + 1) / ((k + 1).factorial : ℝ) = Real.exp x - 1 := by
  have h := (Real.summable_pow_div_factorial x).sum_add_tsum_nat_add 1
  rw [← Real.exp_eq_tsum_pow_div_factorial] at h
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
  linarith

theorem pow_succ_div_factorial_nonneg {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    0 ≤ x ^ (k + 1) / ((k + 1).factorial : ℝ) :=
  div_nonneg (pow_nonneg hx _) (Nat.cast_nonneg _)

/-- `r! k! ≤ (k + r)!`. -/
theorem factorial_mul_factorial_le (r k : ℕ) :
    r.factorial * k.factorial ≤ (k + r).factorial := by
  have h := Nat.add_choose_mul_factorial_mul_factorial k r
  have hc : 1 ≤ (k + r).choose r := Nat.choose_pos (by omega)
  calc r.factorial * k.factorial = 1 * (k.factorial * r.factorial) := by ring
    _ ≤ (k + r).choose r * (k.factorial * r.factorial) := Nat.mul_le_mul_right _ hc
    _ = (k + r).factorial := by rw [← h]; ring

/-- M1b, Lemma 3.9 (tail of the exponential series):
`Σ_{k ≥ r} x^k/k! ≤ (x^r/r!) e^x` for `x ≥ 0`, written with `k = j + r`. -/
theorem tsum_pow_div_factorial_tail_le {x : ℝ} (hx : 0 ≤ x) (r : ℕ) :
    ∑' j : ℕ, x ^ (j + r) / ((j + r).factorial : ℝ) ≤
      x ^ r / (r.factorial : ℝ) * Real.exp x := by
  have hterm : ∀ j : ℕ, x ^ (j + r) / ((j + r).factorial : ℝ) ≤
      x ^ r / (r.factorial : ℝ) * (x ^ j / (j.factorial : ℝ)) := by
    intro j
    rw [pow_add, div_mul_div_comm, mul_comm (x ^ j) (x ^ r)]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    exact_mod_cast factorial_mul_factorial_le r j
  calc ∑' j : ℕ, x ^ (j + r) / ((j + r).factorial : ℝ)
      ≤ ∑' j : ℕ, x ^ r / (r.factorial : ℝ) * (x ^ j / (j.factorial : ℝ)) :=
        ((summable_nat_add_iff r).2 (Real.summable_pow_div_factorial x)).tsum_le_tsum hterm
          ((Real.summable_pow_div_factorial x).mul_left _)
    _ = x ^ r / (r.factorial : ℝ) * Real.exp x := by
        rw [tsum_mul_left, Real.exp_eq_tsum_pow_div_factorial]

/-- M1b, Lemma 4.3 (an elementary estimate): for `r ≥ 1`, `x ≥ 0` and every real `μ`,
`x^r/r! ≤ e^{-μ r} (e^{e^μ x} - 1)` (the sign of `μ` is not used). -/
theorem pow_div_factorial_le_exp_sub {x : ℝ} (hx : 0 ≤ x) (μ : ℝ) {r : ℕ} (hr : 1 ≤ r) :
    x ^ r / (r.factorial : ℝ) ≤ Real.exp (-μ * r) * (Real.exp (Real.exp μ * x) - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have hy : 0 ≤ Real.exp μ * x := mul_nonneg (Real.exp_pos μ).le hx
  have hsum := (summable_nat_add_iff 1).2 (Real.summable_pow_div_factorial (Real.exp μ * x))
  have hterm : (Real.exp μ * x) ^ (m + 1) / ((m + 1).factorial : ℝ) ≤
      ∑' k : ℕ, (Real.exp μ * x) ^ (k + 1) / ((k + 1).factorial : ℝ) :=
    hsum.le_tsum m fun k _ => pow_succ_div_factorial_nonneg hy k
  rw [tsum_pow_succ_div_factorial] at hterm
  have h1 : Real.exp (-μ * ((m + 1 : ℕ) : ℝ)) * Real.exp μ ^ (m + 1) = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add,
      show -μ * ((m + 1 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ) * μ = 0 by ring, Real.exp_zero]
  calc x ^ (m + 1) / ((m + 1).factorial : ℝ)
      = Real.exp (-μ * ((m + 1 : ℕ) : ℝ)) *
          ((Real.exp μ * x) ^ (m + 1) / ((m + 1).factorial : ℝ)) := by
        rw [mul_pow, ← mul_div_assoc, ← mul_assoc, h1, one_mul]
    _ ≤ Real.exp (-μ * ((m + 1 : ℕ) : ℝ)) * (Real.exp (Real.exp μ * x) - 1) :=
        mul_le_mul_of_nonneg_left hterm (Real.exp_pos _).le

/-! ### Decay kernels -/

/-- A decay kernel (M1b, Definition 2.4): `F ≥ 0` with a reproducing constant `C_F > 0`,
`Σ_{z ∈ T'} F(x, z) F(z, y) ≤ C_F F(x, y)` for every finite `T'`. -/
structure DecayKernel (Λ : Type*) where
  /-- The kernel. -/
  F : Λ → Λ → ℝ
  /-- The reproducing constant. -/
  CF : ℝ
  CF_pos : 0 < CF
  F_nonneg : ∀ x y, 0 ≤ F x y
  /-- The reproducing property, in its finite-sum form. -/
  reproducing : ∀ (x y : Λ) (T' : Finset Λ), ∑ z ∈ T', F x z * F z y ≤ CF * F x y

variable {Λ : Type*} {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [Fintype ι] {𝒜 : Net (Set Λ) A} (G : LocalGenerators ι 𝒜)

namespace LocalGenerators

/-- `N_F` is an `F`-bound of the family: `N_F ≥ 0` and `h_{xy} ≤ N_F F(x, y)` for all `x, y`. -/
def IsFBound (K : DecayKernel Λ) (N : ℝ) : Prop := 0 ≤ N ∧ ∀ x y, G.siteMatrix x y ≤ N * K.F x y

/-- M1b, Proposition 3.7: `w_{k+1}(y, x) ≤ N_F^{k+1} C_F^k F(y, x)`. -/
theorem walk_le_decay (K : DecayKernel Λ) {N : ℝ} (hN : G.IsFBound K N) (k : ℕ) (y x : Λ) :
    G.walk (k + 1) y x ≤ N ^ (k + 1) * K.CF ^ k * K.F y x := by
  induction k generalizing y x with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, mul_one]
    by_cases hx : x ∈ G.touched
    · rw [G.walk_one_of_mem hx]; exact hN.2 y x
    · rw [G.walk_eq_zero_of_not_mem_right hx]
      exact mul_nonneg hN.1 (K.F_nonneg y x)
  | succ k ih =>
    rw [walk_succ]
    calc ∑ z ∈ G.touched, G.siteMatrix y z * G.walk (k + 1) z x
        ≤ ∑ z ∈ G.touched, (N * K.F y z) * (N ^ (k + 1) * K.CF ^ k * K.F z x) :=
          Finset.sum_le_sum fun z _ =>
            mul_le_mul (hN.2 y z) (ih z x) (G.walk_nonneg _ z x)
              (mul_nonneg hN.1 (K.F_nonneg y z))
      _ = N ^ (k + 2) * K.CF ^ k * ∑ z ∈ G.touched, K.F y z * K.F z x := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          ring
      _ ≤ N ^ (k + 2) * K.CF ^ k * (K.CF * K.F y x) :=
          mul_le_mul_of_nonneg_left (K.reproducing y x _)
            (mul_nonneg (pow_nonneg hN.1 _) (pow_nonneg K.CF_pos.le _))
      _ = N ^ (k + 1 + 1) * K.CF ^ (k + 1) * K.F y x := by ring

/-- The kernel sum `Φ(Y, X) = Σ_{y ∈ ∂Y} Σ_{x ∈ X ∩ T} F(y, x)`. -/
def kernelSum (K : DecayKernel Λ) (X Y : Set Λ) : ℝ :=
  ∑ y ∈ G.boundary Y, ∑ x ∈ G.regionSites X, K.F y x

theorem kernelSum_nonneg (K : DecayKernel Λ) (X Y : Set Λ) : 0 ≤ G.kernelSum K X Y :=
  Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun x _ => K.F_nonneg y x

/-- `W_{k+1}(Y, X) ≤ N_F^{k+1} C_F^k Φ(Y, X)`. -/
theorem walkSum_le_decay (K : DecayKernel Λ) {N : ℝ} (hN : G.IsFBound K N) (X Y : Set Λ)
    (k : ℕ) : G.walkSum X Y (k + 1) ≤ N ^ (k + 1) * K.CF ^ k * G.kernelSum K X Y := by
  unfold walkSum kernelSum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun x _ => G.walk_le_decay K hN k y x

/-- The terms of the decay series, `Φ/C_F · x^{k+1}/(k+1)!` with `x = 2 N_F C_F t`. -/
def decayTerm (K : DecayKernel Λ) (N : ℝ) (X Y : Set Λ) (t : ℝ) (k : ℕ) : ℝ :=
  G.kernelSum K X Y / K.CF * ((2 * N * K.CF * t) ^ (k + 1) / ((k + 1).factorial : ℝ))

/-- An algebraic identity behind the termwise bound: with `c ≠ 0`,
`a/f · (n b c^k Φ) = Φ/c · ((2 N c t)^{k+1}/f)` once `(2 N c t)^{k+1} = a n c^k c`. -/
theorem decayTerm_eq (K : DecayKernel Λ) (N : ℝ) (X Y : Set Λ) (t : ℝ) (k : ℕ) :
    G.decayTerm K N X Y t k =
      (2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ) *
        (N ^ (k + 1) * K.CF ^ k * G.kernelSum K X Y) := by
  unfold decayTerm
  have hc : K.CF ≠ 0 := K.CF_pos.ne'
  have hf : ((k + 1).factorial : ℝ) ≠ 0 := by positivity
  rw [show (2 * N * K.CF * t) ^ (k + 1) =
    (2 * t) ^ (k + 1) * N ^ (k + 1) * (K.CF ^ k * K.CF) by ring]
  field_simp

/-- The termwise bound of the walk series under a decay kernel. -/
theorem walkTerm_le_decayTerm (K : DecayKernel Λ) {N : ℝ} (hN : G.IsFBound K N) (X Y : Set Λ)
    {t : ℝ} (ht : 0 ≤ t) (k : ℕ) : G.walkTerm X Y t k ≤ G.decayTerm K N X Y t k := by
  rw [decayTerm_eq]
  unfold walkTerm coef
  exact mul_le_mul_of_nonneg_left (G.walkSum_le_decay K hN X Y k) (coef_nonneg k ht)

theorem summable_decayTerm (K : DecayKernel Λ) (N : ℝ) (X Y : Set Λ) (t : ℝ) :
    Summable (G.decayTerm K N X Y t) := by
  have h := (Real.summable_pow_div_factorial (2 * N * K.CF * t)).mul_left
    (G.kernelSum K X Y / K.CF)
  rw [← summable_nat_add_iff 1] at h
  exact h

theorem tsum_decayTerm (K : DecayKernel Λ) (N : ℝ) (X Y : Set Λ) (t : ℝ) :
    ∑' k, G.decayTerm K N X Y t k =
      (Real.exp (2 * N * K.CF * t) - 1) / K.CF * G.kernelSum K X Y := by
  unfold decayTerm
  rw [tsum_mul_left, tsum_pow_succ_div_factorial]
  ring

/-- The walk series under a decay kernel:
`Σ_{k ≥ 1} (2t)^k/k! W_k(Y, X) ≤ (e^{2 N_F C_F t} - 1)/C_F · Φ(Y, X)`. -/
theorem tsum_walkTerm_le_decay (K : DecayKernel Λ) {N : ℝ} (hN : G.IsFBound K N) (X Y : Set Λ)
    {t : ℝ} (ht : 0 ≤ t) :
    ∑' k, G.walkTerm X Y t k ≤
      (Real.exp (2 * N * K.CF * t) - 1) / K.CF * G.kernelSum K X Y := by
  rw [← G.tsum_decayTerm K N X Y t]
  exact (G.summable_walkTerm X Y ht).tsum_le_tsum (G.walkTerm_le_decayTerm K hN X Y ht)
    (G.summable_decayTerm K N X Y t)

open Classical in
/-- M1b, Theorem 3.8 (closed form (ii), decay functions):
`‖[A(t), b]‖ ≤ 2‖a‖‖b‖ ([X ∩ Y ≠ ∅] + (e^{2 N_F C_F t} - 1)/C_F · Φ(Y, X))` with
`Φ(Y, X) = Σ_{y ∈ ∂Y} Σ_{x ∈ X ∩ T} F(y, x)`. -/
theorem liebRobinson_decay (hc : Net.IsCausal (latticeIndex Λ) 𝒜) (K : DecayKernel Λ) {N : ℝ}
    (hN : G.IsFBound K N) (X Y : Set Λ) {a b : A} (ha : a ∈ 𝒜 X) (hb : b ∈ 𝒜 Y) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖comm (G.evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
        (Real.exp (2 * N * K.CF * t) - 1) / K.CF * G.kernelSum K X Y) := by
  refine (G.liebRobinson_walk hc X Y ha hb ht).trans ?_
  have hab : 0 ≤ 2 * ‖a‖ * ‖b‖ := by positivity
  exact mul_le_mul_of_nonneg_left
    (add_le_add (le_refl _) (G.tsum_walkTerm_le_decay K hN X Y ht)) hab

/-! ### Bounded geometry -/

open Classical in
/-- The number of terms whose support contains `u`. -/
def degreeAt (u : Λ) : ℕ := (Finset.univ.filter fun i => u ∈ G.supp i).card

open Classical in
theorem sum_ind_eq_degreeAt (u : Λ) : ∑ i, G.ind i u = (G.degreeAt u : ℝ) :=
  G.sum_ind_eq_card u

/-- Bounded geometry `(g, ℓ, R, ρ)` of a family (M1b, Definition 2.5), with respect to a
distance `d` satisfying `d(u, u) = 0` and the triangle inequality: every site lies in at most
`g` supports, every strength is at most `ℓ ≥ 0`, every support has at most `R` sites and
diameter at most `ρ ≥ 0`. -/
structure BoundedGeometry where
  /-- The distance. -/
  d : Λ → Λ → ℝ
  d_self : ∀ u, d u u = 0
  d_triangle : ∀ u v w, d u w ≤ d u v + d v w
  /-- The degree bound. -/
  g : ℕ
  /-- The strength bound. -/
  ell : ℝ
  ell_nonneg : 0 ≤ ell
  /-- The size bound. -/
  R : ℕ
  /-- The diameter bound. -/
  rho : ℝ
  rho_nonneg : 0 ≤ rho
  degree : ∀ u, G.degreeAt u ≤ g
  strength : ∀ i, G.kappa i ≤ ell
  size : ∀ i, (G.supp i).card ≤ R
  diam : ∀ i, ∀ u ∈ G.supp i, ∀ v ∈ G.supp i, d u v ≤ rho

namespace BoundedGeometry

variable {G} (B : G.BoundedGeometry)

/-- The row-sum bound `M = g ℓ R`. -/
def M : ℝ := B.g * B.ell * B.R

theorem M_nonneg : 0 ≤ B.M :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) B.ell_nonneg) (Nat.cast_nonneg _)

/-- The velocity `v = 2 g ℓ R = 2M`. -/
def v : ℝ := 2 * B.M

theorem v_nonneg : 0 ≤ B.v := mul_nonneg (by norm_num) B.M_nonneg

/-- M1b, Proposition 4.1(a): `w_k(y, x) = 0` whenever `k ρ < d(y, x)`. -/
theorem walk_eq_zero_of_dist (k : ℕ) {y x : Λ} (h : (k : ℝ) * B.rho < B.d y x) :
    G.walk k y x = 0 := by
  induction k generalizing y with
  | zero =>
    rw [Nat.cast_zero, zero_mul] at h
    have hyx : y ≠ x := fun hyx => by rw [hyx, B.d_self] at h; exact lt_irrefl _ h
    exact G.walk_zero_of_ne hyx
  | succ k ih =>
    rw [walk_succ]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hyz : G.siteMatrix y z = 0
    · rw [hyz, zero_mul]
    · have hd : B.d y z ≤ B.rho := by
        classical
        rw [G.siteMatrix_eq_sum_filter] at hyz
        obtain ⟨i, hi, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hyz
        obtain ⟨_, hyi, hzi⟩ := Finset.mem_filter.1 hi
        exact B.diam i y hyi z hzi
      have hzx : (k : ℝ) * B.rho < B.d z x := by
        have := B.d_triangle y z x
        push_cast at h
        linarith
      rw [ih hzx, mul_zero]

/-- M1b, Proposition 4.1(b): the row sums of `h` are at most `M = g ℓ R`. -/
theorem sum_siteMatrix_le (u : Λ) (s : Finset Λ) : ∑ v ∈ s, G.siteMatrix u v ≤ B.M := by
  unfold siteMatrix
  rw [Finset.sum_comm]
  have hterm : ∀ i, ∑ v ∈ s, G.kappa i * G.ind i u * G.ind i v ≤
      G.ind i u * (B.ell * B.R) := by
    intro i
    rw [← Finset.mul_sum]
    calc G.kappa i * G.ind i u * ∑ v ∈ s, G.ind i v
        ≤ B.ell * G.ind i u * (B.R : ℝ) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (B.strength i) (G.ind_nonneg i u))
            ((G.sum_ind_le_card i s).trans (by exact_mod_cast B.size i))
            (G.sum_ind_nonneg i s)
            (mul_nonneg B.ell_nonneg (G.ind_nonneg i u))
      _ = G.ind i u * (B.ell * B.R) := by ring
  calc ∑ i, ∑ v ∈ s, G.kappa i * G.ind i u * G.ind i v
      ≤ ∑ i, G.ind i u * (B.ell * B.R) := Finset.sum_le_sum fun i _ => hterm i
    _ = (G.degreeAt u : ℝ) * (B.ell * B.R) := by rw [← Finset.sum_mul, G.sum_ind_eq_degreeAt]
    _ ≤ B.g * (B.ell * B.R) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast B.degree u)
          (mul_nonneg B.ell_nonneg (Nat.cast_nonneg _))
    _ = B.M := by unfold M; ring

/-- `W_k(Y, X) = 0` when every pair `y ∈ ∂Y`, `x ∈ X ∩ T` is farther than `kρ`. -/
theorem walkSum_eq_zero_of_dist (X Y : Set Λ) (k : ℕ)
    (hd : ∀ y ∈ G.boundary Y, ∀ x ∈ G.regionSites X, (k : ℝ) * B.rho < B.d y x) :
    G.walkSum X Y k = 0 :=
  Finset.sum_eq_zero fun y hy => Finset.sum_eq_zero fun x hx =>
    B.walk_eq_zero_of_dist k (hd y hy x hx)

/-- The walk series under bounded geometry, beyond `r ≥ 1` steps:
`Σ_{k ≥ 1} (2t)^k/k! W_k(Y, X) ≤ |∂Y| (vt)^r e^{vt}/r!` when every pair of sites is farther
than `(r - 1)ρ`. -/
theorem tsum_walkTerm_le_geom (X Y : Set Λ) {m : ℕ}
    (hd : ∀ y ∈ G.boundary Y, ∀ x ∈ G.regionSites X, (m : ℝ) * B.rho < B.d y x) {t : ℝ}
    (ht : 0 ≤ t) :
    ∑' k, G.walkTerm X Y t k ≤
      (G.boundary Y).card *
        ((B.v * t) ^ (m + 1) / ((m + 1).factorial : ℝ) * Real.exp (B.v * t)) := by
  have hsum := G.summable_walkTerm X Y ht
  have hgeom : Summable fun j : ℕ =>
      (G.boundary Y).card * ((B.v * t) ^ (j + (m + 1)) / ((j + (m + 1)).factorial : ℝ)) := by
    have h := (Real.summable_pow_div_factorial (B.v * t)).mul_left ((G.boundary Y).card : ℝ)
    rw [← summable_nat_add_iff (m + 1)] at h
    exact h
  -- the first `m` terms vanish
  have hzero : ∀ k < m, G.walkTerm X Y t k = 0 := by
    intro k hk
    unfold walkTerm
    rw [B.walkSum_eq_zero_of_dist X Y (k + 1) fun y hy x hx => ?_, mul_zero]
    refine lt_of_le_of_lt ?_ (hd y hy x hx)
    have hk' : ((k + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hk
    exact mul_le_mul_of_nonneg_right hk' B.rho_nonneg
  have hsplit := hsum.sum_add_tsum_nat_add m
  rw [Finset.sum_eq_zero fun k hk => hzero k (Finset.mem_range.1 hk), zero_add] at hsplit
  rw [← hsplit]
  -- the tail is bounded termwise by `|∂Y| (vt)^{j+m+1}/(j+m+1)!`
  have htail : ∀ j, G.walkTerm X Y t (j + m) ≤
      (G.boundary Y).card * ((B.v * t) ^ (j + (m + 1)) / ((j + (m + 1)).factorial : ℝ)) := by
    intro j
    have h := G.walkTerm_le_of_rowSum B.M_nonneg (fun u => B.sum_siteMatrix_le u _) X Y ht (j + m)
    rw [show j + m + 1 = j + (m + 1) by ring] at h
    refine h.trans (le_of_eq ?_)
    congr 2
    unfold v
    ring
  have hvt : 0 ≤ B.v * t := mul_nonneg B.v_nonneg ht
  calc ∑' j, G.walkTerm X Y t (j + m)
      ≤ ∑' j, (G.boundary Y).card *
          ((B.v * t) ^ (j + (m + 1)) / ((j + (m + 1)).factorial : ℝ)) :=
        ((summable_nat_add_iff m).2 hsum).tsum_le_tsum htail hgeom
    _ = (G.boundary Y).card *
          ∑' j, (B.v * t) ^ (j + (m + 1)) / ((j + (m + 1)).factorial : ℝ) := tsum_mul_left
    _ ≤ (G.boundary Y).card *
          ((B.v * t) ^ (m + 1) / ((m + 1).factorial : ℝ) * Real.exp (B.v * t)) :=
        mul_le_mul_of_nonneg_left (tsum_pow_div_factorial_tail_le hvt (m + 1))
          (Nat.cast_nonneg _)

end BoundedGeometry

open Classical in
/-- M1b, Theorem 4.2 (closed form (iii), bounded geometry): if every site of `∂Y` is farther
than `(r - 1)ρ` from every site of `X ∩ T` (`r ≥ 1`), then
`‖[A(t), b]‖ ≤ 2‖a‖‖b‖ ([X ∩ Y ≠ ∅] + |∂Y| (vt)^r e^{vt}/r!)` with `v = 2gℓR`. -/
theorem liebRobinson_boundedGeometry (hc : Net.IsCausal (latticeIndex Λ) 𝒜)
    (B : G.BoundedGeometry) (X Y : Set Λ) {r : ℕ} (hr : 1 ≤ r)
    (hd : ∀ y ∈ G.boundary Y, ∀ x ∈ G.regionSites X, ((r : ℝ) - 1) * B.rho < B.d y x)
    {a b : A} (ha : a ∈ 𝒜 X) (hb : b ∈ 𝒜 Y) {t : ℝ} (ht : 0 ≤ t) :
    ‖comm (G.evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
        (G.boundary Y).card * ((B.v * t) ^ r / (r.factorial : ℝ) * Real.exp (B.v * t))) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have hd' : ∀ y ∈ G.boundary Y, ∀ x ∈ G.regionSites X, (m : ℝ) * B.rho < B.d y x := by
    intro y hy x hx
    have := hd y hy x hx
    push_cast at this
    simpa using this
  refine (G.liebRobinson_walk hc X Y ha hb ht).trans ?_
  have hab : 0 ≤ 2 * ‖a‖ * ‖b‖ := by positivity
  exact mul_le_mul_of_nonneg_left
    (add_le_add (le_refl _) (B.tsum_walkTerm_le_geom X Y hd' ht)) hab

open Classical in
/-- M1b, Theorem 4.4 (closed form (iv), the exponential light cone): under the hypotheses of
Theorem 4.2, for every real `μ` (the sign of `μ` is not used),
`‖[A(t), b]‖ ≤ 2‖a‖‖b‖ ([X ∩ Y ≠ ∅] + |∂Y| e^{vt} e^{-μ r} (e^{e^μ v t} - 1))`. -/
theorem liebRobinson_cone (hc : Net.IsCausal (latticeIndex Λ) 𝒜)
    (B : G.BoundedGeometry) (X Y : Set Λ) {r : ℕ} (hr : 1 ≤ r)
    (hd : ∀ y ∈ G.boundary Y, ∀ x ∈ G.regionSites X, ((r : ℝ) - 1) * B.rho < B.d y x)
    (μ : ℝ) {a b : A} (ha : a ∈ 𝒜 X) (hb : b ∈ 𝒜 Y) {t : ℝ} (ht : 0 ≤ t) :
    ‖comm (G.evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
        (G.boundary Y).card * (Real.exp (B.v * t) *
          (Real.exp (-μ * r) * (Real.exp (Real.exp μ * (B.v * t)) - 1)))) := by
  refine (G.liebRobinson_boundedGeometry hc B X Y hr hd ha hb ht).trans ?_
  have hab : 0 ≤ 2 * ‖a‖ * ‖b‖ := by positivity
  refine mul_le_mul_of_nonneg_left (add_le_add (le_refl _) ?_) hab
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  rw [mul_comm (Real.exp (B.v * t))]
  exact mul_le_mul_of_nonneg_right
    (pow_div_factorial_le_exp_sub (mul_nonneg B.v_nonneg ht) μ hr) (Real.exp_pos _).le

end LocalGenerators

end LocalityLean

end
