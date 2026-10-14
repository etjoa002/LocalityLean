/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import LocalityLean.Core.Bound
import Mathlib.Analysis.Matrix.Normed

/-!
# The site matrix and the walk series (M1b, closed form (i))

The site matrix of a family of local generators is `h_{uv} = Σ_{i : u ∈ S_i, v ∈ S_i} κ_i`
(M1b, Definition 2.2), a function on pairs of sites; no finiteness of the site type is assumed.
The `k`-step walk weight `w_k(y, x)` is defined by the recursion
`w_0(y, x) = [y = x]`, `w_{k+1}(y, x) = Σ_{z ∈ T} h_{yz} w_k(z, x)` over the finite set `T` of
touched sites (Definition 2.3), and `W_k(Y, X) = Σ_{y ∈ ∂Y} Σ_{x ∈ X ∩ T} w_k(y, x)` with `∂Y` the
sites of `Y` touched by a term crossing `Y` (Definition 2.1).

The domination theorem (M1b, Theorem 3.4) bounds the path count by the walk weight,
`P_k(Y, X) ≤ W_k(Y, X)`, by a counting argument on the recursion of the path count; the walk
series (Theorem 3.6) follows from the path-sum bound of M1a.

## Main definitions

* `LocalityLean.LocalGenerators.touched`, `boundary`, `siteMatrix`, `walk`, `walkSum`.
* `LocalityLean.LocalGenerators.walkTerm` (the terms of the walk series).

## Main statements

* `LocalityLean.LocalGenerators.pathSumRec_le_walkSum` (Theorem 3.4).
* `LocalityLean.LocalGenerators.liebRobinson_walk` (Theorem 3.6).
-/

noncomputable section

namespace LocalityLean

open LinearAQFT Finset

variable {Λ : Type*} {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [Fintype ι] {𝒜 : Net (Set Λ) A} (G : LocalGenerators ι 𝒜)

namespace LocalGenerators

/-! ### Touched sites, the site matrix -/

open Classical in
/-- The touched sites `T = ⋃_i S_i` (M1b, Definition 2.1). -/
def touched : Finset Λ := Finset.univ.biUnion G.supp

theorem mem_touched {u : Λ} : u ∈ G.touched ↔ ∃ i, u ∈ G.supp i := by
  classical
  simp [touched]

theorem supp_subset_touched (i : ι) : G.supp i ⊆ G.touched := fun _ hu =>
  G.mem_touched.2 ⟨i, hu⟩

open Classical in
/-- The indicator `[u ∈ S_i]` as a real number. -/
def ind (i : ι) (u : Λ) : ℝ := if u ∈ G.supp i then 1 else 0

theorem ind_nonneg (i : ι) (u : Λ) : 0 ≤ G.ind i u := by
  unfold ind; split_ifs <;> norm_num

theorem ind_le_one (i : ι) (u : Λ) : G.ind i u ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

theorem ind_of_mem {i : ι} {u : Λ} (hu : u ∈ G.supp i) : G.ind i u = 1 := by
  unfold ind; simp [hu]

theorem ind_of_not_mem {i : ι} {u : Λ} (hu : u ∉ G.supp i) : G.ind i u = 0 := by
  unfold ind; simp [hu]

/-- The site matrix `h_{uv} = Σ_i κ_i [u ∈ S_i] [v ∈ S_i]` (M1b, Definition 2.2). -/
def siteMatrix (u v : Λ) : ℝ := ∑ i, G.kappa i * G.ind i u * G.ind i v

open Classical in
theorem siteMatrix_eq_sum_filter (u v : Λ) :
    G.siteMatrix u v = ∑ i ∈ Finset.univ.filter (fun i => u ∈ G.supp i ∧ v ∈ G.supp i),
      G.kappa i := by
  unfold siteMatrix
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold ind
  split_ifs with h1 h2 h3 <;> simp_all

theorem siteMatrix_nonneg (u v : Λ) : 0 ≤ G.siteMatrix u v :=
  Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (G.kappa_nonneg i) (G.ind_nonneg i u))
    (G.ind_nonneg i v)

theorem siteMatrix_comm (u v : Λ) : G.siteMatrix u v = G.siteMatrix v u := by
  unfold siteMatrix
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem siteMatrix_eq_zero_of_not_mem_left {u v : Λ} (hu : u ∉ G.touched) :
    G.siteMatrix u v = 0 :=
  Finset.sum_eq_zero fun i _ => by
    rw [G.ind_of_not_mem fun h => hu (G.supp_subset_touched i h)]; ring

theorem siteMatrix_eq_zero_of_not_mem_right {u v : Λ} (hv : v ∉ G.touched) :
    G.siteMatrix u v = 0 := by
  rw [G.siteMatrix_comm]; exact G.siteMatrix_eq_zero_of_not_mem_left hv

/-- `K_1 = Σ_i κ_i |S_i|`, the weighted size of the family. -/
def weightedSize : ℝ := ∑ i, G.kappa i * (G.supp i).card

theorem weightedSize_nonneg : 0 ≤ G.weightedSize :=
  Finset.sum_nonneg fun i _ => mul_nonneg (G.kappa_nonneg i) (Nat.cast_nonneg _)

theorem sum_ind_le_card (i : ι) (s : Finset Λ) : ∑ u ∈ s, G.ind i u ≤ (G.supp i).card := by
  classical
  calc ∑ u ∈ s, G.ind i u = ∑ u ∈ s.filter (· ∈ G.supp i), (1 : ℝ) := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun u _ => by unfold ind; rfl
    _ = ((s.filter (· ∈ G.supp i)).card : ℝ) := by simp
    _ ≤ (G.supp i).card := by
        exact_mod_cast Finset.card_le_card (fun u hu => (Finset.mem_filter.1 hu).2)

theorem sum_ind_nonneg (i : ι) (s : Finset Λ) : 0 ≤ ∑ u ∈ s, G.ind i u :=
  Finset.sum_nonneg fun u _ => G.ind_nonneg i u

/-- Row sums: `Σ_{v ∈ T} h_{uv} ≤ K_1` (M1b, Proposition 3.1(c)); more generally over any
finite set of columns. -/
theorem sum_siteMatrix_le (u : Λ) (s : Finset Λ) :
    ∑ v ∈ s, G.siteMatrix u v ≤ G.weightedSize := by
  unfold siteMatrix weightedSize
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.mul_sum]
  calc G.kappa i * G.ind i u * ∑ v ∈ s, G.ind i v
      ≤ G.kappa i * 1 * (G.supp i).card :=
        mul_le_mul (mul_le_mul_of_nonneg_left (G.ind_le_one i u) (G.kappa_nonneg i))
          (G.sum_ind_le_card i s) (G.sum_ind_nonneg i s)
          (mul_nonneg (G.kappa_nonneg i) zero_le_one)
    _ = G.kappa i * (G.supp i).card := by ring

/-! ### Walk weights -/

open Classical in
/-- The walk weight `w_k(y, x)` (M1b, Definition 2.3): `w_0(y, x) = [y = x]` and
`w_{k+1}(y, x) = Σ_{z ∈ T} h_{yz} w_k(z, x)`. -/
def walk : ℕ → Λ → Λ → ℝ
  | 0, y, x => if y = x then 1 else 0
  | k + 1, y, x => ∑ z ∈ G.touched, G.siteMatrix y z * walk k z x

theorem walk_zero_self (y : Λ) : G.walk 0 y y = 1 := by
  simp [walk]

theorem walk_zero_of_ne {y x : Λ} (h : y ≠ x) : G.walk 0 y x = 0 := by
  simp [walk, h]

theorem walk_succ (k : ℕ) (y x : Λ) :
    G.walk (k + 1) y x = ∑ z ∈ G.touched, G.siteMatrix y z * G.walk k z x := by
  simp [walk]

theorem walk_zero_nonneg (y x : Λ) : 0 ≤ G.walk 0 y x := by
  by_cases h : y = x
  · subst h; rw [G.walk_zero_self]; exact zero_le_one
  · rw [G.walk_zero_of_ne h]

theorem walk_nonneg (k : ℕ) (y x : Λ) : 0 ≤ G.walk k y x := by
  induction k generalizing y x with
  | zero => exact G.walk_zero_nonneg y x
  | succ k ih =>
    rw [walk_succ]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (G.siteMatrix_nonneg y z) (ih z x)

theorem walk_eq_zero_of_not_mem_left {k : ℕ} {y x : Λ} (hy : y ∉ G.touched) :
    G.walk (k + 1) y x = 0 := by
  rw [walk_succ]
  exact Finset.sum_eq_zero fun z _ => by rw [G.siteMatrix_eq_zero_of_not_mem_left hy, zero_mul]

theorem walk_eq_zero_of_not_mem_right {k : ℕ} {y x : Λ} (hx : x ∉ G.touched) :
    G.walk (k + 1) y x = 0 := by
  induction k generalizing y with
  | zero =>
    rw [walk_succ]
    refine Finset.sum_eq_zero fun z hz => ?_
    have hzx : z ≠ x := fun h => hx (h ▸ hz)
    rw [G.walk_zero_of_ne hzx, mul_zero]
  | succ k ih =>
    rw [walk_succ]
    exact Finset.sum_eq_zero fun z _ => by rw [ih, mul_zero]

/-- `Σ_{x ∈ s} w_0(y, x) ≤ 1` for any finite `s`. -/
theorem sum_walk_zero_le (y : Λ) (s : Finset Λ) : ∑ x ∈ s, G.walk 0 y x ≤ 1 := by
  by_cases hy : y ∈ s
  · rw [Finset.sum_eq_single y (fun x _ hx => G.walk_zero_of_ne (Ne.symm hx))
      (fun h => absurd hy h), walk_zero_self]
  · rw [Finset.sum_eq_zero fun x hx => G.walk_zero_of_ne fun h => hy (by rw [h]; exact hx)]
    exact zero_le_one

/-- `Σ_{x ∈ T} w_k(y, x) ≤ M^k` whenever every row sum of `h` over `T` is at most `M ≥ 0`. -/
theorem sum_walk_le_of_rowSum {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ u, ∑ v ∈ G.touched, G.siteMatrix u v ≤ M) (k : ℕ) (y : Λ) :
    ∑ x ∈ G.touched, G.walk k y x ≤ M ^ k := by
  induction k generalizing y with
  | zero => rw [pow_zero]; exact G.sum_walk_zero_le y _
  | succ k ih =>
    simp only [walk_succ]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    calc ∑ z ∈ G.touched, G.siteMatrix y z * ∑ x ∈ G.touched, G.walk k z x
        ≤ ∑ z ∈ G.touched, G.siteMatrix y z * M ^ k :=
          Finset.sum_le_sum fun z _ =>
            mul_le_mul_of_nonneg_left (ih z) (G.siteMatrix_nonneg y z)
      _ = (∑ z ∈ G.touched, G.siteMatrix y z) * M ^ k := by rw [Finset.sum_mul]
      _ ≤ M * M ^ k := mul_le_mul_of_nonneg_right (hM y) (pow_nonneg hM0 k)
      _ = M ^ (k + 1) := by ring

/-- `Σ_{x ∈ T} w_k(y, x) ≤ K_1^k` (M1b, Proposition 3.2(c)). -/
theorem sum_walk_le (k : ℕ) (y : Λ) : ∑ x ∈ G.touched, G.walk k y x ≤ G.weightedSize ^ k :=
  G.sum_walk_le_of_rowSum G.weightedSize_nonneg (fun u => G.sum_siteMatrix_le u _) k y

/-! ### The boundary and the walk sum -/

open Classical in
/-- The boundary `∂Y = Y ∩ ⋃_{i crosses Y} S_i` (M1b, Definition 2.1). -/
def boundary (Y : Set Λ) : Finset Λ := ((G.crosses Y).biUnion G.supp).filter (· ∈ Y)

theorem mem_boundary {Y : Set Λ} {y : Λ} :
    y ∈ G.boundary Y ↔ y ∈ Y ∧ ∃ i ∈ G.crosses Y, y ∈ G.supp i := by
  classical
  simp only [boundary, Finset.mem_filter, Finset.mem_biUnion]
  tauto

theorem boundary_subset_touched (Y : Set Λ) : G.boundary Y ⊆ G.touched := fun y hy => by
  obtain ⟨_, i, _, hi⟩ := G.mem_boundary.1 hy
  exact G.supp_subset_touched i hi

theorem boundary_supp_subset (i : ι) : G.boundary (G.supp i : Set Λ) ⊆ G.supp i := fun _ hy =>
  (G.mem_boundary.1 hy).1

open Classical in
/-- The sites of `X` touched by the family, `X ∩ T`. -/
def regionSites (X : Set Λ) : Finset Λ := G.touched.filter (· ∈ X)

theorem mem_regionSites {X : Set Λ} {x : Λ} : x ∈ G.regionSites X ↔ x ∈ G.touched ∧ x ∈ X := by
  classical
  simp [regionSites]

theorem regionSites_subset_touched (X : Set Λ) : G.regionSites X ⊆ G.touched := fun _ hx =>
  (G.mem_regionSites.1 hx).1

/-- `W_k(Y, X) = Σ_{y ∈ ∂Y} Σ_{x ∈ X ∩ T} w_k(y, x)` (M1b, Definition 2.3). -/
def walkSum (X Y : Set Λ) (k : ℕ) : ℝ :=
  ∑ y ∈ G.boundary Y, ∑ x ∈ G.regionSites X, G.walk k y x

theorem walkSum_nonneg (X Y : Set Λ) (k : ℕ) : 0 ≤ G.walkSum X Y k :=
  Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun x _ => G.walk_nonneg k y x

/-- `W_k(Y, X) ≤ |∂Y| M^k` whenever every row sum of `h` over `T` is at most `M ≥ 0`. -/
theorem walkSum_le_of_rowSum {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ u, ∑ v ∈ G.touched, G.siteMatrix u v ≤ M) (X Y : Set Λ) (k : ℕ) :
    G.walkSum X Y k ≤ (G.boundary Y).card * M ^ k := by
  unfold walkSum
  calc ∑ y ∈ G.boundary Y, ∑ x ∈ G.regionSites X, G.walk k y x
      ≤ ∑ y ∈ G.boundary Y, ∑ x ∈ G.touched, G.walk k y x :=
        Finset.sum_le_sum fun y _ =>
          Finset.sum_le_sum_of_subset_of_nonneg (G.regionSites_subset_touched X)
            fun x _ _ => G.walk_nonneg k y x
    _ ≤ ∑ _y ∈ G.boundary Y, M ^ k :=
        Finset.sum_le_sum fun y _ => G.sum_walk_le_of_rowSum hM0 hM k y
    _ = (G.boundary Y).card * M ^ k := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- `W_k(Y, X) ≤ |∂Y| K_1^k`. -/
theorem walkSum_le (X Y : Set Λ) (k : ℕ) :
    G.walkSum X Y k ≤ (G.boundary Y).card * G.weightedSize ^ k :=
  G.walkSum_le_of_rowSum G.weightedSize_nonneg (fun u => G.sum_siteMatrix_le u _) X Y k

open Classical in
/-- `Σ_i [u ∈ S_i]` is the number of terms containing `u`. -/
theorem sum_ind_eq_card (u : Λ) :
    ∑ i, G.ind i u = ((Finset.univ.filter fun i => u ∈ G.supp i).card : ℝ) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold ind
  split_ifs <;> simp

/-! ### The domination theorem -/

/-- A nonempty fiber: if some `u ∈ s` lies in `S_i`, the count `Σ_{v ∈ s} [v ∈ S_i]` is at
least one. -/
theorem one_le_sum_ind {i : ι} {s : Finset Λ} {u : Λ} (hu : u ∈ s) (hi : u ∈ G.supp i) :
    1 ≤ ∑ v ∈ s, G.ind i v := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := G.ind i)
    (Finset.singleton_subset_iff.2 hu) (fun v _ _ => G.ind_nonneg i v)
  rw [Finset.sum_singleton, G.ind_of_mem hi] at h
  exact h

/-- A site of `S_i ∩ Y` lies on the boundary `∂Y` when `i` crosses `Y`. -/
theorem mem_boundary_of_crosses {Y : Set Λ} {i : ι} (hi : i ∈ G.crosses Y) {y : Λ}
    (hy : y ∈ G.supp i) (hyY : y ∈ Y) : y ∈ G.boundary Y :=
  G.mem_boundary.2 ⟨hyY, i, hi, hy⟩

/-- `Σ_{y ∈ s} Σ_{x ∈ s'} h_{yx} = Σ_i κ_i (Σ_{y ∈ s} [y ∈ S_i]) (Σ_{x ∈ s'} [x ∈ S_i])`. -/
theorem sum_sum_siteMatrix (s s' : Finset Λ) :
    ∑ y ∈ s, ∑ x ∈ s', G.siteMatrix y x =
      ∑ i, G.kappa i * (∑ y ∈ s, G.ind i y) * (∑ x ∈ s', G.ind i x) := by
  unfold siteMatrix
  calc ∑ y ∈ s, ∑ x ∈ s', ∑ i, G.kappa i * G.ind i y * G.ind i x
      = ∑ y ∈ s, ∑ i, ∑ x ∈ s', G.kappa i * G.ind i y * G.ind i x :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ y ∈ s, ∑ x ∈ s', G.kappa i * G.ind i y * G.ind i x := Finset.sum_comm
    _ = ∑ i, G.kappa i * (∑ y ∈ s, G.ind i y) * (∑ x ∈ s', G.ind i x) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring

/-- `w_1(y, x) = h_{yx}` for `x ∈ T`. -/
theorem walk_one_of_mem {y x : Λ} (hx : x ∈ G.touched) : G.walk 1 y x = G.siteMatrix y x := by
  rw [walk_succ, Finset.sum_eq_single x
    (fun z _ hz => by rw [G.walk_zero_of_ne hz, mul_zero]) (fun h => absurd hx h),
    walk_zero_self, mul_one]

/-- The base case of the domination, `P_1(Y, X) ≤ W_1(Y, X)`. -/
theorem pathSumRec_one_le_walkSum (X Y : Set Λ) : G.pathSumRec X 1 Y ≤ G.walkSum X Y 1 := by
  rw [pathSumRec_one]
  unfold walkSum
  have hW : ∑ y ∈ G.boundary Y, ∑ x ∈ G.regionSites X, G.walk 1 y x =
      ∑ i, G.kappa i * (∑ y ∈ G.boundary Y, G.ind i y) * (∑ x ∈ G.regionSites X, G.ind i x) := by
    rw [← G.sum_sum_siteMatrix]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x hx => ?_
    exact G.walk_one_of_mem (G.mem_regionSites.1 hx).1
  rw [hW]
  calc ∑ i ∈ G.bridge X Y, G.kappa i
      ≤ ∑ i ∈ G.bridge X Y,
          G.kappa i * (∑ y ∈ G.boundary Y, G.ind i y) * (∑ x ∈ G.regionSites X, G.ind i x) := by
        refine Finset.sum_le_sum fun i hi => ?_
        obtain ⟨hcr, hX⟩ := G.mem_bridge.1 hi
        obtain ⟨y, hyS, hyY⟩ := hcr.1
        obtain ⟨x, hxS, hxX⟩ := hX
        have hy : y ∈ G.boundary Y :=
          G.mem_boundary_of_crosses (G.mem_crosses.2 hcr) hyS hyY
        have hx : x ∈ G.regionSites X :=
          G.mem_regionSites.2 ⟨G.supp_subset_touched i hxS, hxX⟩
        have h1 := G.one_le_sum_ind hy hyS
        have h2 := G.one_le_sum_ind hx hxS
        calc G.kappa i = G.kappa i * 1 * 1 := by ring
          _ ≤ G.kappa i * (∑ y ∈ G.boundary Y, G.ind i y) *
              (∑ x ∈ G.regionSites X, G.ind i x) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 (G.kappa_nonneg i)) h2 zero_le_one
              (mul_nonneg (G.kappa_nonneg i) (G.sum_ind_nonneg i _))
    _ ≤ ∑ i, G.kappa i * (∑ y ∈ G.boundary Y, G.ind i y) *
          (∑ x ∈ G.regionSites X, G.ind i x) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => ?_
        exact mul_nonneg (mul_nonneg (G.kappa_nonneg i) (G.sum_ind_nonneg i _))
          (G.sum_ind_nonneg i _)

/-- The sum of walk weights from `z` into `X ∩ T`, `V(z) = Σ_{x ∈ X ∩ T} w_k(z, x)`. -/
def walkInto (X : Set Λ) (k : ℕ) (z : Λ) : ℝ := ∑ x ∈ G.regionSites X, G.walk k z x

theorem walkInto_nonneg (X : Set Λ) (k : ℕ) (z : Λ) : 0 ≤ G.walkInto X k z :=
  Finset.sum_nonneg fun x _ => G.walk_nonneg k z x

theorem walkSum_eq_sum_walkInto (X Y : Set Λ) (k : ℕ) :
    G.walkSum X Y k = ∑ y ∈ G.boundary Y, G.walkInto X k y := rfl

/-- A sum over `S_i` as a sum over `T` with the indicator. -/
theorem sum_supp_eq_sum_touched_ind (i : ι) (f : Λ → ℝ) :
    ∑ z ∈ G.supp i, f z = ∑ z ∈ G.touched, G.ind i z * f z := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not G.touched (· ∈ G.supp i)]
  have h0 : ∑ z ∈ G.touched.filter (fun z => z ∉ G.supp i), G.ind i z * f z = 0 :=
    Finset.sum_eq_zero fun z hz => by
      rw [G.ind_of_not_mem (Finset.mem_filter.1 hz).2, zero_mul]
  rw [h0, add_zero]
  have h4 : G.touched.filter (fun z => z ∈ G.supp i) = G.supp i := by
    ext z
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨G.supp_subset_touched i h, h⟩⟩
  rw [h4]
  exact Finset.sum_congr rfl fun z hz => by rw [G.ind_of_mem hz, one_mul]

/-- `W_{k+1}(Y, X) = Σ_i κ_i (Σ_{y ∈ ∂Y} [y ∈ S_i]) Σ_{z ∈ S_i} V(z)`. -/
theorem walkSum_succ_eq (X Y : Set Λ) (k : ℕ) :
    G.walkSum X Y (k + 1) =
      ∑ i, G.kappa i * (∑ y ∈ G.boundary Y, G.ind i y) * ∑ z ∈ G.supp i, G.walkInto X k z := by
  set a : ι → ℝ := fun i => ∑ y ∈ G.boundary Y, G.ind i y with ha
  have h2 : ∀ z, ∑ y ∈ G.boundary Y, G.siteMatrix y z = ∑ i, G.kappa i * a i * G.ind i z := by
    intro z
    unfold siteMatrix
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ha]
    rw [Finset.mul_sum, Finset.sum_mul]
  unfold walkSum
  simp_rw [walk_succ]
  calc ∑ y ∈ G.boundary Y, ∑ x ∈ G.regionSites X, ∑ z ∈ G.touched,
        G.siteMatrix y z * G.walk k z x
      = ∑ y ∈ G.boundary Y, ∑ z ∈ G.touched, ∑ x ∈ G.regionSites X,
          G.siteMatrix y z * G.walk k z x :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ z ∈ G.touched, ∑ y ∈ G.boundary Y, ∑ x ∈ G.regionSites X,
          G.siteMatrix y z * G.walk k z x := Finset.sum_comm
    _ = ∑ z ∈ G.touched, (∑ y ∈ G.boundary Y, G.siteMatrix y z) * G.walkInto X k z := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [walkInto, Finset.sum_mul]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ z ∈ G.touched, ∑ i, G.kappa i * a i * G.ind i z * G.walkInto X k z := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [h2, Finset.sum_mul]
    _ = ∑ i, ∑ z ∈ G.touched, G.kappa i * a i * G.ind i z * G.walkInto X k z :=
        Finset.sum_comm
    _ = ∑ i, G.kappa i * a i * ∑ z ∈ G.touched, G.ind i z * G.walkInto X k z := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum G.touched]
        apply Finset.sum_congr rfl
        intro z _
        ring
    _ = ∑ i, G.kappa i * a i * ∑ z ∈ G.supp i, G.walkInto X k z := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [G.sum_supp_eq_sum_touched_ind i]

/-- M1b, Theorem 3.4 (domination of the path count): `P_k(Y, X) ≤ W_k(Y, X)` for `k ≥ 1`. -/
theorem pathSumRec_le_walkSum (X : Set Λ) (k : ℕ) (hk : 1 ≤ k) (Y : Set Λ) :
    G.pathSumRec X k Y ≤ G.walkSum X Y k := by
  induction k, hk using Nat.le_induction generalizing Y with
  | base => exact G.pathSumRec_one_le_walkSum X Y
  | succ k hk ih =>
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [G.pathSumRec_succ_succ X Y m, G.walkSum_succ_eq X Y (m + 1)]
    have hV : ∀ i, 0 ≤ ∑ z ∈ G.supp i, G.walkInto X (m + 1) z := fun i =>
      Finset.sum_nonneg fun z _ => G.walkInto_nonneg X _ z
    calc ∑ i ∈ G.through X Y, G.kappa i * G.pathSumRec X (m + 1) (G.supp i)
        ≤ ∑ i ∈ G.through X Y, G.kappa i * ∑ z ∈ G.supp i, G.walkInto X (m + 1) z := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (G.kappa_nonneg i)
          calc G.pathSumRec X (m + 1) (G.supp i) ≤ G.walkSum X (G.supp i) (m + 1) := ih _
            _ ≤ ∑ z ∈ G.supp i, G.walkInto X (m + 1) z := by
                rw [walkSum_eq_sum_walkInto]
                exact Finset.sum_le_sum_of_subset_of_nonneg (G.boundary_supp_subset i)
                  fun z _ _ => G.walkInto_nonneg X _ z
      _ ≤ ∑ i ∈ G.through X Y, G.kappa i * (∑ y ∈ G.boundary Y, G.ind i y) *
            ∑ z ∈ G.supp i, G.walkInto X (m + 1) z := by
          refine Finset.sum_le_sum fun i hi => ?_
          obtain ⟨hcr, _⟩ := G.mem_through.1 hi
          obtain ⟨y, hyS, hyY⟩ := hcr.1
          have h1 := G.one_le_sum_ind
            (G.mem_boundary_of_crosses (G.mem_crosses.2 hcr) hyS hyY) hyS
          calc G.kappa i * ∑ z ∈ G.supp i, G.walkInto X (m + 1) z
              = G.kappa i * 1 * ∑ z ∈ G.supp i, G.walkInto X (m + 1) z := by ring
            _ ≤ G.kappa i * (∑ y ∈ G.boundary Y, G.ind i y) *
                ∑ z ∈ G.supp i, G.walkInto X (m + 1) z := by
                refine mul_le_mul_of_nonneg_right ?_ (hV i)
                exact mul_le_mul_of_nonneg_left h1 (G.kappa_nonneg i)
      _ ≤ ∑ i, G.kappa i * (∑ y ∈ G.boundary Y, G.ind i y) *
            ∑ z ∈ G.supp i, G.walkInto X (m + 1) z :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ =>
            mul_nonneg (mul_nonneg (G.kappa_nonneg i) (G.sum_ind_nonneg i _)) (hV i)

/-! ### The walk series (closed form (i)) -/

/-- The terms of the walk series, `(2t)^{k+1}/(k+1)! · W_{k+1}(Y, X)`. -/
def walkTerm (X Y : Set Λ) (t : ℝ) (k : ℕ) : ℝ := coef k t * G.walkSum X Y (k + 1)

theorem walkTerm_nonneg (X Y : Set Λ) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    0 ≤ G.walkTerm X Y t k :=
  mul_nonneg (coef_nonneg k ht) (G.walkSum_nonneg X Y _)

theorem seriesTerm_le_walkTerm (X Y : Set Λ) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    G.seriesTerm X Y t k ≤ G.walkTerm X Y t k :=
  mul_le_mul_of_nonneg_left (G.pathSumRec_le_walkSum X (k + 1) (Nat.succ_pos k) Y)
    (coef_nonneg k ht)

theorem walkTerm_le_of_rowSum {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ u, ∑ v ∈ G.touched, G.siteMatrix u v ≤ M) (X Y : Set Λ) {t : ℝ} (ht : 0 ≤ t)
    (k : ℕ) :
    G.walkTerm X Y t k ≤
      (G.boundary Y).card * ((2 * t * M) ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
  unfold walkTerm coef
  calc (2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ) * G.walkSum X Y (k + 1)
      ≤ (2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ) *
          ((G.boundary Y).card * M ^ (k + 1)) :=
        mul_le_mul_of_nonneg_left (G.walkSum_le_of_rowSum hM0 hM X Y (k + 1)) (coef_nonneg k ht)
    _ = (G.boundary Y).card * ((2 * t * M) ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
        rw [mul_pow]; ring

theorem walkTerm_le (X Y : Set Λ) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    G.walkTerm X Y t k ≤
      (G.boundary Y).card * ((2 * t * G.weightedSize) ^ (k + 1) / ((k + 1).factorial : ℝ)) :=
  G.walkTerm_le_of_rowSum G.weightedSize_nonneg (fun u => G.sum_siteMatrix_le u _) X Y ht k

/-- The walk series converges. -/
theorem summable_walkTerm (X Y : Set Λ) {t : ℝ} (ht : 0 ≤ t) : Summable (G.walkTerm X Y t) := by
  have h := (Real.summable_pow_div_factorial (2 * t * G.weightedSize)).mul_left
    ((G.boundary Y).card : ℝ)
  rw [← summable_nat_add_iff 1] at h
  exact Summable.of_nonneg_of_le (G.walkTerm_nonneg X Y ht) (G.walkTerm_le X Y ht) h

theorem tsum_seriesTerm_le_tsum_walkTerm (X Y : Set Λ) {t : ℝ} (ht : 0 ≤ t) :
    ∑' k, G.seriesTerm X Y t k ≤ ∑' k, G.walkTerm X Y t k :=
  (G.summable_seriesTerm X Y ht).tsum_le_tsum (G.seriesTerm_le_walkTerm X Y ht)
    (G.summable_walkTerm X Y ht)

open Classical in
/-- M1b, Theorem 3.6 (closed form (i), the walk series):
`‖[A(t), b]‖ ≤ 2‖a‖‖b‖ ([X ∩ Y ≠ ∅] + Σ_{k ≥ 0} walkTerm k)`, where
`Σ_{k ≥ 0} walkTerm k = Σ_{k ≥ 1} (2t)^k/k! W_k(Y, X)` by reindexing. -/
theorem liebRobinson_walk (hc : Net.IsCausal (latticeIndex Λ) 𝒜) (X Y : Set Λ) {a b : A}
    (ha : a ∈ 𝒜 X) (hb : b ∈ 𝒜 Y) {t : ℝ} (ht : 0 ≤ t) :
    ‖comm (G.evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) + ∑' k, G.walkTerm X Y t k) := by
  refine (G.liebRobinson hc X Y ha hb ht).trans ?_
  have hab : 0 ≤ 2 * ‖a‖ * ‖b‖ := by positivity
  exact mul_le_mul_of_nonneg_left
    (add_le_add (le_refl _) (G.tsum_seriesTerm_le_tsum_walkTerm X Y ht)) hab

open Classical in
/-- M1b, Theorem 3.6 in the supremum form. -/
theorem commBound_le_walk (hc : Net.IsCausal (latticeIndex Λ) 𝒜) (X Y : Set Λ) {t : ℝ}
    (ht : 0 ≤ t) :
    G.commBound X Y t ≤
      2 * ((if (X ∩ Y).Nonempty then 1 else 0) + ∑' k, G.walkTerm X Y t k) :=
  (G.commBound_le hc X Y ht).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl _) (G.tsum_seriesTerm_le_tsum_walkTerm X Y ht)) (by norm_num))

/-! ### The finite lattice: matrix powers and the matrix exponential -/

/-- The site matrix as a matrix (meaningful on a finite site type). -/
def toMatrix : Matrix Λ Λ ℝ := Matrix.of fun u v => G.siteMatrix u v

theorem toMatrix_apply (u v : Λ) : G.toMatrix u v = G.siteMatrix u v := rfl

section Finite

variable [Fintype Λ] [DecidableEq Λ]

/-- M1b, Proposition 3.5(a): `w_k(y, x) = (h^k)_{yx}`. -/
theorem walk_eq_pow_apply (k : ℕ) (y x : Λ) : G.walk k y x = (G.toMatrix ^ k) y x := by
  induction k generalizing y x with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    by_cases h : y = x
    · subst h; simp [G.walk_zero_self]
    · simp [G.walk_zero_of_ne h, h]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply, walk_succ]
    calc ∑ z ∈ G.touched, G.siteMatrix y z * G.walk k z x
        = ∑ z ∈ G.touched, G.toMatrix y z * (G.toMatrix ^ k) z x :=
          Finset.sum_congr rfl fun z _ => by rw [ih, toMatrix_apply]
      _ = ∑ z, G.toMatrix y z * (G.toMatrix ^ k) z x :=
          Finset.sum_subset (Finset.subset_univ _) fun z _ hz => by
            rw [toMatrix_apply, G.siteMatrix_eq_zero_of_not_mem_right hz, zero_mul]

open scoped Matrix.Norms.Operator in
set_option backward.isDefEq.respectTransparency false in
/-- M1b, Proposition 3.5(b): the entries of the matrix exponential are the exponential series of
the entries of the powers, `(e^{sh})_{yx} = Σ_n s^n/n! (h^n)_{yx}`. -/
theorem hasSum_exp_apply (s : ℝ) (y x : Λ) :
    HasSum (fun n : ℕ => s ^ n / (n.factorial : ℝ) * (G.toMatrix ^ n) y x)
      (NormedSpace.exp (s • G.toMatrix) y x) := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (s • G.toMatrix)
  have h2 := Pi.hasSum.1 (Pi.hasSum.1 h y) x
  convert h2 using 1
  funext n
  simp only [Matrix.smul_apply, smul_pow, smul_eq_mul]
  rw [div_eq_inv_mul]
  ring

theorem summable_exp_apply (s : ℝ) (y x : Λ) :
    Summable (fun n : ℕ => s ^ n / (n.factorial : ℝ) * (G.toMatrix ^ n) y x) :=
  (G.hasSum_exp_apply s y x).summable

/-- M1b, Proposition 3.5(c): `Σ_{k ≥ 1} s^k/k! (h^k)_{yx} = (e^{sh} - 1)_{yx}`. -/
theorem tsum_exp_apply_succ (s : ℝ) (y x : Λ) :
    ∑' k : ℕ, s ^ (k + 1) / ((k + 1).factorial : ℝ) * (G.toMatrix ^ (k + 1)) y x =
      NormedSpace.exp (s • G.toMatrix) y x - (1 : Matrix Λ Λ ℝ) y x := by
  have h := (G.summable_exp_apply s y x).sum_add_tsum_nat_add 1
  rw [(G.hasSum_exp_apply s y x).tsum_eq] at h
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    one_mul] at h
  linarith

/-- The walk series on a finite lattice, as entries of the matrix exponential:
`Σ_{k ≥ 1} (2t)^k/k! W_k(Y, X) = Σ_{y ∈ ∂Y} Σ_{x ∈ X ∩ T} (e^{2th} - 1)_{yx}`. -/
theorem tsum_walkTerm_eq (X Y : Set Λ) (t : ℝ) :
    ∑' k, G.walkTerm X Y t k =
      ∑ y ∈ G.boundary Y, ∑ x ∈ G.regionSites X,
        (NormedSpace.exp ((2 * t) • G.toMatrix) y x - (1 : Matrix Λ Λ ℝ) y x) := by
  have hterm : ∀ k, G.walkTerm X Y t k = ∑ y ∈ G.boundary Y, ∑ x ∈ G.regionSites X,
      (2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ) * (G.toMatrix ^ (k + 1)) y x := by
    intro k
    unfold walkTerm walkSum coef
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [G.walk_eq_pow_apply]
  have hsum : ∀ y x, Summable fun k : ℕ =>
      (2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ) * (G.toMatrix ^ (k + 1)) y x := fun y x =>
    (summable_nat_add_iff 1).2 (G.summable_exp_apply (2 * t) y x)
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum fun y _ => (summable_sum fun x _ => hsum y x)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Summable.tsum_finsetSum fun x _ => hsum y x]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact G.tsum_exp_apply_succ (2 * t) y x

open Classical in
/-- M1b, Theorem 3.6 on a finite lattice: the review's matrix form,
`‖[A(t), b]‖ ≤ 2‖a‖‖b‖ ([X ∩ Y ≠ ∅] + Σ_{y ∈ ∂Y} Σ_{x ∈ X ∩ T} (e^{2th} - 1)_{yx})`. -/
theorem liebRobinson_matrixExp (hc : Net.IsCausal (latticeIndex Λ) 𝒜) (X Y : Set Λ) {a b : A}
    (ha : a ∈ 𝒜 X) (hb : b ∈ 𝒜 Y) {t : ℝ} (ht : 0 ≤ t) :
    ‖comm (G.evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
        ∑ y ∈ G.boundary Y, ∑ x ∈ G.regionSites X,
          (NormedSpace.exp ((2 * t) • G.toMatrix) y x - (1 : Matrix Λ Λ ℝ) y x)) := by
  rw [← G.tsum_walkTerm_eq X Y t]
  exact G.liebRobinson_walk hc X Y ha hb ht

end Finite

end LocalGenerators

end LocalityLean

end
