/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import LocalityLean.Core.Generator
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Paths and the path count

A first-contact path of length `k` from the probe's region `Y` to the observable's region `X`
is a sequence of indices whose first support crosses the boundary of `Y`, whose consecutive
supports each cross the boundary of the previous one (meet it and are not contained in it),
which avoid `X` before the last step, and whose last support meets `X` (M1a, Definition 2.2:
the perturbation at each Duhamel step is the family of terms crossing the current region). The
path count `P_k(Y, X)` is defined by the recursion the proof
of the master lemma uses (M1a, Definition 2.3) and proved equal to the weighted sum over paths
(M1a, Proposition 3.10), and bounded by `K^k`.

Region arguments are the observable's region first, then the probe's: `pathSum X Y k`,
`bridge X Y`, `through X Y`; the recursion `pathSumRec X k Y` keeps `X` fixed and varies the
probe's region.

## Main definitions

* `LocalityLean.LocalGenerators.IsPath`, `pathSum` (the explicit sum).
* `LocalityLean.LocalGenerators.bridge`, `through`, `pathSumRec` (the recursion).

## Main statements

* `LocalityLean.LocalGenerators.pathSum_eq_pathSumRec`, `pathSumRec_nonneg`, `pathSumRec_le`.
-/

noncomputable section

namespace LocalityLean

open LinearAQFT

variable {Λ : Type*} {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [Fintype ι] {𝒜 : Net (Set Λ) A} (G : LocalGenerators ι 𝒜)

namespace LocalGenerators

/-- A first-contact path of length `k` from `Y` to `X` (M1a, Definition 2.2): the first support
crosses `Y`, each support crosses the previous one, no support before the last meets `X`, and
the last support meets `X`. There is no path of length `0`. -/
def IsPath (X Y : Set Λ) : {k : ℕ} → (Fin k → ι) → Prop
  | 0, _ => False
  | k + 1, p =>
      Crosses (G.supp (p 0) : Set Λ) Y ∧
      (∀ j : Fin k, Crosses (G.supp (p j.succ) : Set Λ) (G.supp (p j.castSucc) : Set Λ)) ∧
      (∀ j : Fin k, Disjoint (G.supp (p j.castSucc) : Set Λ) X) ∧
      ((G.supp (p (Fin.last k)) : Set Λ) ∩ X).Nonempty

open Classical in
/-- The weighted count of paths of length `k` as an explicit sum: `Σ_{paths} Π_j κ_{i_j}`. -/
def pathSum (X Y : Set Λ) (k : ℕ) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (Fin k → ι)).filter (G.IsPath X Y), ∏ j, G.kappa (p j)

open Classical in
/-- The indices whose support crosses `Y` and meets `X`: a path of length one. -/
def bridge (X Y : Set Λ) : Finset ι :=
  Finset.univ.filter fun i => Crosses (G.supp i : Set Λ) Y ∧ ((G.supp i : Set Λ) ∩ X).Nonempty

open Classical in
/-- The indices whose support crosses `Y` and misses `X`: a path may continue through them. -/
def through (X Y : Set Λ) : Finset ι :=
  Finset.univ.filter fun i => Crosses (G.supp i : Set Λ) Y ∧ Disjoint (G.supp i : Set Λ) X

/-- The path count by recursion (M1a, Definition 2.3): `P_1(Y,X) = Σ_{bridge} κ_i`,
`P_{k+1}(Y,X) = Σ_{i ∈ through(Y,X)} κ_i P_k(S_i, X)`; `P_0 = 0`. -/
def pathSumRec (X : Set Λ) : ℕ → Set Λ → ℝ
  | 0, _ => 0
  | 1, Y => ∑ i ∈ G.bridge X Y, G.kappa i
  | k + 2, Y => ∑ i ∈ G.through X Y, G.kappa i * pathSumRec X (k + 1) (G.supp i)

theorem mem_bridge {X Y : Set Λ} {i : ι} :
    i ∈ G.bridge X Y ↔ Crosses (G.supp i : Set Λ) Y ∧ ((G.supp i : Set Λ) ∩ X).Nonempty := by
  simp [bridge]

theorem mem_through {X Y : Set Λ} {i : ι} :
    i ∈ G.through X Y ↔ Crosses (G.supp i : Set Λ) Y ∧ Disjoint (G.supp i : Set Λ) X := by
  simp [through]

theorem bridge_subset_crosses (X Y : Set Λ) : G.bridge X Y ⊆ G.crosses Y := fun _ hi =>
  G.mem_crosses.mpr (G.mem_bridge.mp hi).1

theorem through_subset_crosses (X Y : Set Λ) : G.through X Y ⊆ G.crosses Y := fun _ hi =>
  G.mem_crosses.mpr (G.mem_through.mp hi).1

theorem disjoint_bridge_through (X Y : Set Λ) : Disjoint (G.bridge X Y) (G.through X Y) := by
  rw [Finset.disjoint_left]
  intro i hb ht
  rw [mem_bridge] at hb
  rw [mem_through] at ht
  exact (Set.not_disjoint_iff_nonempty_inter.mpr hb.2) ht.2

/-- The indices crossing `Y` are the bridges and the throughs. -/
theorem crosses_eq_bridge_union_through [DecidableEq ι] (X Y : Set Λ) :
    G.crosses Y = G.bridge X Y ∪ G.through X Y := by
  ext i
  simp only [mem_crosses, Finset.mem_union, mem_bridge, mem_through]
  constructor
  · intro h
    by_cases hX : ((G.supp i : Set Λ) ∩ X).Nonempty
    · exact Or.inl ⟨h, hX⟩
    · exact Or.inr ⟨h, Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hX)⟩
  · rintro (h | h) <;> exact h.1

theorem pathSumRec_zero (X Y : Set Λ) : G.pathSumRec X 0 Y = 0 := by
  simp only [pathSumRec]

theorem pathSumRec_one (X Y : Set Λ) : G.pathSumRec X 1 Y = ∑ i ∈ G.bridge X Y, G.kappa i := by
  simp only [pathSumRec]

theorem pathSumRec_succ_succ (X Y : Set Λ) (k : ℕ) :
    G.pathSumRec X (k + 2) Y =
      ∑ i ∈ G.through X Y, G.kappa i * G.pathSumRec X (k + 1) (G.supp i) := by
  simp only [pathSumRec]

/-- The recursion in the form `k + 1 + 1`, as sums over `range (n + 1)` produce it. -/
theorem pathSumRec_succ_succ' (X Y : Set Λ) (k : ℕ) :
    G.pathSumRec X (k + 1 + 1) Y =
      ∑ i ∈ G.through X Y, G.kappa i * G.pathSumRec X (k + 1) (G.supp i) :=
  G.pathSumRec_succ_succ X Y k

theorem pathSumRec_nonneg (X : Set Λ) (k : ℕ) (Y : Set Λ) : 0 ≤ G.pathSumRec X k Y := by
  induction k using Nat.strong_induction_on generalizing Y with
  | _ k ih =>
    match k with
    | 0 => exact le_rfl
    | 1 => exact Finset.sum_nonneg fun i _ => G.kappa_nonneg i
    | k + 2 =>
      rw [pathSumRec_succ_succ]
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (G.kappa_nonneg i) (ih (k + 1) (by omega) _)

/-- M1a, Proposition 3.10: `P_k(Y, X) ≤ K^k` with `K = Σ_i κ_i`. -/
theorem pathSumRec_le (X : Set Λ) (k : ℕ) (Y : Set Λ) :
    G.pathSumRec X k Y ≤ G.totalStrength ^ k := by
  induction k using Nat.strong_induction_on generalizing Y with
  | _ k ih =>
    match k with
    | 0 => simp [pathSumRec_zero]
    | 1 => simpa [pathSumRec_one] using G.sum_kappa_le_totalStrength (G.bridge X Y)
    | k + 2 =>
      rw [pathSumRec_succ_succ, pow_succ']
      calc ∑ i ∈ G.through X Y, G.kappa i * G.pathSumRec X (k + 1) (G.supp i)
          ≤ ∑ i ∈ G.through X Y, G.kappa i * G.totalStrength ^ (k + 1) :=
            Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (ih (k + 1) (by omega) _) (G.kappa_nonneg i)
        _ = (∑ i ∈ G.through X Y, G.kappa i) * G.totalStrength ^ (k + 1) := by
            rw [Finset.sum_mul]
        _ ≤ G.totalStrength * G.totalStrength ^ (k + 1) :=
            mul_le_mul_of_nonneg_right (G.sum_kappa_le_totalStrength _)
              (pow_nonneg G.totalStrength_nonneg _)

/-- A path of length `k + 2` is an index `i` crossing `Y` and missing `X`, followed by a path of
length `k + 1` from `S_i` to `X`. -/
theorem isPath_cons_iff (X Y : Set Λ) {k : ℕ} (i : ι) (q : Fin (k + 1) → ι) :
    G.IsPath X Y (Fin.cons i q : Fin (k + 2) → ι) ↔
      (Crosses (G.supp i : Set Λ) Y ∧ Disjoint (G.supp i : Set Λ) X) ∧
        G.IsPath X (G.supp i) q := by
  simp only [IsPath, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero,
    Fin.castSucc_succ, ← Fin.succ_last]
  tauto

/-- The explicit sum of length one. -/
theorem pathSum_one (X Y : Set Λ) : G.pathSum X Y 1 = ∑ i ∈ G.bridge X Y, G.kappa i := by
  classical
  unfold pathSum bridge
  rw [Finset.sum_filter, Finset.sum_filter, ← Equiv.sum_comp (Equiv.funUnique (Fin 1) ι).symm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [IsPath]

/-- The explicit sum of length `k + 2`, split at the first step. -/
theorem pathSum_succ_succ (X Y : Set Λ) (k : ℕ) :
    G.pathSum X Y (k + 2) = ∑ i ∈ G.through X Y, G.kappa i * G.pathSum X (G.supp i) (k + 1) := by
  classical
  unfold pathSum through
  simp only [Finset.sum_filter]
  rw [← Equiv.sum_comp (Fin.consEquiv fun _ => ι), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, isPath_cons_iff, Fin.prod_univ_succ, Fin.cons_zero,
    Fin.cons_succ]
  by_cases hi : Crosses (G.supp i : Set Λ) Y ∧ Disjoint (G.supp i : Set Λ) X
  · simp only [hi, true_and, ite_true, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs <;> simp
  · simp only [hi, false_and, ite_false, Finset.sum_const_zero]

/-- M1a, Proposition 3.10: the recursion counts the first-contact paths. -/
theorem pathSum_eq_pathSumRec (X Y : Set Λ) (k : ℕ) :
    G.pathSum X Y (k + 1) = G.pathSumRec X (k + 1) Y := by
  induction k generalizing Y with
  | zero => rw [pathSum_one, pathSumRec_one]
  | succ k ih =>
    rw [pathSum_succ_succ, pathSumRec_succ_succ]
    exact Finset.sum_congr rfl fun i _ => by rw [ih]

end LocalGenerators

end LocalityLean

end
