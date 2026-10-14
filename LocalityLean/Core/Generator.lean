/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import LocalityLean.Core.Support
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Local generators

The commutator seminorm `commNorm 𝒜 S c = sup {‖[c, b]‖ : b ∈ 𝒜 S, ‖b‖ ≤ 1}` (M1a, eq. (1)),
its properties (M1a, Proposition 3.1), and a finite family of bounded local generators on a net
with the three hypotheses of the master lemma (M1a, Definition 2.1): (G1) locality in the
argument, (G2) support closure, (G3) contraction of every sub-family. The dynamics is
`evolve t = exp (t • total)`.

## Main definitions

* `LocalityLean.comm`, `LocalityLean.commNorm`.
* `LocalityLean.Crosses` (a set meets a region and its complement).
* `LocalityLean.LocalGenerators`, with `total`, `subfamily`, `evolve`, `crosses`.

## Main statements

* `commNorm_nonneg`, `commNorm_le_two_mul_norm`, `norm_comm_le_commNorm`,
  `commNorm_eq_zero_of_commute`, `commNorm_mono`, `commNorm_add_le`, `commNorm_smul`.
* `LocalGenerators.norm_evolve_le`, `LocalGenerators.subfamily_union`,
  `LocalGenerators.total_eq_crosses_add_compl` (M1a, Proposition 3.2); `comm_eq_lie`.
-/

noncomputable section

namespace LocalityLean

open LinearAQFT

variable {Λ : Type*} {A : Type*} [CStarAlgebra A]

/-- The commutator `[a, b] = a b - b a`. -/
def comm (a b : A) : A := a * b - b * a

theorem comm_def (a b : A) : comm a b = a * b - b * a := rfl

/-- The commutator is Mathlib's ring Lie bracket `⁅a, b⁆` (kept as a local name for readable
statements; a reuse decision of the library design). -/
theorem comm_eq_lie (a b : A) : comm a b = ⁅a, b⁆ := (Ring.lie_def a b).symm

theorem norm_comm_le (a b : A) : ‖comm a b‖ ≤ 2 * ‖a‖ * ‖b‖ := by
  calc ‖comm a b‖ ≤ ‖a * b‖ + ‖b * a‖ := norm_sub_le _ _
    _ ≤ ‖a‖ * ‖b‖ + ‖b‖ * ‖a‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖a‖ * ‖b‖ := by ring

theorem comm_eq_zero_of_commute {a b : A} (h : Commute a b) : comm a b = 0 := by
  simp [comm, h.eq]

theorem comm_add_left (a a' b : A) : comm (a + a') b = comm a b + comm a' b := by
  simp only [comm]; noncomm_ring

theorem comm_smul_left (r : ℂ) (a b : A) : comm (r • a) b = r • comm a b := by
  simp only [comm, smul_mul_assoc, mul_smul_comm, smul_sub]

theorem comm_smul_right (r : ℂ) (a b : A) : comm a (r • b) = r • comm a b := by
  simp only [comm, smul_mul_assoc, mul_smul_comm, smul_sub]

theorem comm_zero_right (a : A) : comm a 0 = 0 := by simp [comm]

theorem comm_sub_left (a a' b : A) : comm (a - a') b = comm a b - comm a' b := by
  simp only [comm]; noncomm_ring

/-- The set of commutator norms over the unit ball of the local algebra of `S`. -/
def commSet (𝒜 : Net (Set Λ) A) (S : Set Λ) (c : A) : Set ℝ :=
  (fun b => ‖comm c b‖) '' {b | b ∈ 𝒜 S ∧ ‖b‖ ≤ 1}

/-- The commutator seminorm of G1 (M1a, eq. (1)): the supremum of `‖[c, b]‖` over `b` in the
algebra of `S` with `‖b‖ ≤ 1`. -/
def commNorm (𝒜 : Net (Set Λ) A) (S : Set Λ) (c : A) : ℝ :=
  sSup (commSet 𝒜 S c)

variable (𝒜 : Net (Set Λ) A) (S : Set Λ)

theorem commSet_nonempty (c : A) : (commSet 𝒜 S c).Nonempty :=
  ⟨‖comm c 0‖, 0, ⟨zero_mem _, by simp⟩, rfl⟩

theorem commSet_bddAbove (c : A) : BddAbove (commSet 𝒜 S c) := by
  refine ⟨2 * ‖c‖, ?_⟩
  rintro _ ⟨b, ⟨-, hb⟩, rfl⟩
  calc ‖comm c b‖ ≤ 2 * ‖c‖ * ‖b‖ := norm_comm_le c b
    _ ≤ 2 * ‖c‖ * 1 := by gcongr
    _ = 2 * ‖c‖ := mul_one _

/-- `‖[c, b]‖ ≤ commNorm 𝒜 S c` for `b` in the unit ball of the algebra of `S`. -/
theorem norm_comm_le_commNorm {c b : A} (hb : b ∈ 𝒜 S) (hb1 : ‖b‖ ≤ 1) :
    ‖comm c b‖ ≤ commNorm 𝒜 S c :=
  le_csSup (commSet_bddAbove 𝒜 S c) ⟨b, ⟨hb, hb1⟩, rfl⟩

/-- `commNorm 𝒜 S c ≤ M` as soon as every commutator norm over the unit ball is at most `M`. -/
theorem commNorm_le_of_forall {c : A} {M : ℝ}
    (h : ∀ b ∈ 𝒜 S, ‖b‖ ≤ 1 → ‖comm c b‖ ≤ M) : commNorm 𝒜 S c ≤ M :=
  csSup_le (commSet_nonempty 𝒜 S c) (by rintro _ ⟨b, ⟨hb, hb1⟩, rfl⟩; exact h b hb hb1)

/-- M1a, Proposition 3.1 (a): nonnegativity. -/
theorem commNorm_nonneg (c : A) : 0 ≤ commNorm 𝒜 S c :=
  le_trans (norm_nonneg _) (norm_comm_le_commNorm 𝒜 S (zero_mem _) (by simp))

/-- M1a, Proposition 3.1 (a): the bound `2‖c‖`. -/
theorem commNorm_le_two_mul_norm (c : A) : commNorm 𝒜 S c ≤ 2 * ‖c‖ :=
  commNorm_le_of_forall 𝒜 S fun b _ hb1 =>
    calc ‖comm c b‖ ≤ 2 * ‖c‖ * ‖b‖ := norm_comm_le c b
      _ ≤ 2 * ‖c‖ * 1 := by gcongr
      _ = 2 * ‖c‖ := mul_one _

/-- M1a, Proposition 3.1 (b): zero on elements commuting with the local algebra. -/
theorem commNorm_eq_zero_of_commute {c : A} (h : ∀ b ∈ 𝒜 S, Commute c b) :
    commNorm 𝒜 S c = 0 :=
  le_antisymm (commNorm_le_of_forall 𝒜 S fun b hb _ => by simp [comm_eq_zero_of_commute (h b hb)])
    (commNorm_nonneg 𝒜 S c)

/-- M1a, Proposition 3.1 (c): monotone in the region. -/
theorem commNorm_mono {S S' : Set Λ} (hS : S ⊆ S') (c : A) :
    commNorm 𝒜 S c ≤ commNorm 𝒜 S' c :=
  commNorm_le_of_forall 𝒜 S fun _ hb hb1 => norm_comm_le_commNorm 𝒜 S' (𝒜.mono hS hb) hb1

/-- M1a, Proposition 3.1 (d): subadditivity. -/
theorem commNorm_add_le (c c' : A) : commNorm 𝒜 S (c + c') ≤ commNorm 𝒜 S c + commNorm 𝒜 S c' :=
  commNorm_le_of_forall 𝒜 S fun b hb hb1 => by
    rw [comm_add_left]
    exact (norm_add_le _ _).trans
      (add_le_add (norm_comm_le_commNorm 𝒜 S hb hb1) (norm_comm_le_commNorm 𝒜 S hb hb1))

/-- M1a, Proposition 3.1 (d): absolute homogeneity. -/
theorem commNorm_smul (r : ℂ) (c : A) : commNorm 𝒜 S (r • c) = ‖r‖ * commNorm 𝒜 S c := by
  rcases eq_or_ne r 0 with rfl | hr
  · have h0 : commNorm 𝒜 S (0 : A) = 0 :=
      commNorm_eq_zero_of_commute 𝒜 S fun b _ => Commute.zero_left b
    simp [h0]
  · apply le_antisymm
    · refine commNorm_le_of_forall 𝒜 S fun b hb hb1 => ?_
      rw [comm_smul_left, norm_smul]
      exact mul_le_mul_of_nonneg_left (norm_comm_le_commNorm 𝒜 S hb hb1) (norm_nonneg r)
    · have hr' : 0 < ‖r‖ := norm_pos_iff.mpr hr
      rw [← le_div_iff₀' hr']
      refine commNorm_le_of_forall 𝒜 S fun b hb hb1 => ?_
      rw [le_div_iff₀' hr', ← norm_smul, ← comm_smul_left]
      exact norm_comm_le_commNorm 𝒜 S hb hb1

/-- Lipschitz continuity in the argument: `|N(c) - N(c')| ≤ 2‖c - c'‖`. -/
theorem abs_commNorm_sub_le (c c' : A) :
    |commNorm 𝒜 S c - commNorm 𝒜 S c'| ≤ 2 * ‖c - c'‖ := by
  rw [abs_sub_le_iff]
  constructor
  · have := commNorm_add_le 𝒜 S (c - c') c'
    rw [sub_add_cancel] at this
    linarith [commNorm_le_two_mul_norm 𝒜 S (c - c')]
  · have := commNorm_add_le 𝒜 S (c' - c) c
    rw [sub_add_cancel] at this
    rw [norm_sub_rev] at *
    linarith [commNorm_le_two_mul_norm 𝒜 S (c' - c)]

/-- `Crosses S Y`: the set `S` meets `Y` and is not contained in it, that is, it meets the
boundary of `Y`. The perturbation of the master lemma at a probe region `Y` is the family of
terms whose support crosses `Y`. -/
def Crosses (S Y : Set Λ) : Prop := (S ∩ Y).Nonempty ∧ ¬ S ⊆ Y

/-- A finite family of bounded local generators on the net `𝒜` (M1a, Definition 2.1): supports,
bounded maps, strengths, and the three hypotheses of the master lemma. -/
structure LocalGenerators (ι : Type*) [Fintype ι] (𝒜 : Net (Set Λ) A) where
  /-- The support of the `i`-th term. -/
  supp : ι → Finset Λ
  /-- The `i`-th generator, a bounded linear map of the ambient algebra. -/
  L : ι → (A →L[ℂ] A)
  /-- The strength `κ_i` of the `i`-th term. -/
  kappa : ι → ℝ
  kappa_nonneg : ∀ i, 0 ≤ kappa i
  /-- (G1) locality in the argument: `‖L_i c‖ ≤ κ_i sup {‖[c, b]‖ : b ∈ 𝒜(S_i), ‖b‖ ≤ 1}`. -/
  local_in_arg : ∀ i c, ‖L i c‖ ≤ kappa i * commNorm 𝒜 (↑(supp i)) c
  /-- (G2) support closure: `L_i` maps the algebra of `Z` into the algebra of `Z ∪ S_i`. -/
  maps_into : ∀ i (Z : Set Λ), ∀ a ∈ 𝒜 Z, L i a ∈ 𝒜 (Z ∪ ↑(supp i))
  /-- (G3) contraction: every sub-family generates a contraction semigroup for `t ≥ 0`. -/
  contraction : ∀ (J : Finset ι) (t : ℝ), 0 ≤ t → ‖NormedSpace.exp (t • ∑ i ∈ J, L i)‖ ≤ 1

namespace LocalGenerators

variable {ι : Type*} [Fintype ι] {𝒜 : Net (Set Λ) A} (G : LocalGenerators ι 𝒜)

/-- The generator of the sub-family `J`, `L_J = Σ_{i ∈ J} L_i`. -/
def subfamily (J : Finset ι) : A →L[ℂ] A := ∑ i ∈ J, G.L i

/-- The full generator `L = Σ_i L_i`. -/
def total : A →L[ℂ] A := G.subfamily Finset.univ

/-- The Heisenberg dynamics `e^{tL}`. -/
def evolve (t : ℝ) : A →L[ℂ] A := NormedSpace.exp (t • G.total)

open Classical in
/-- The indices whose support crosses the boundary of `Y`: meets `Y` and is not inside it. -/
def crosses (Y : Set Λ) : Finset ι := Finset.univ.filter fun i => Crosses (G.supp i : Set Λ) Y

/-- The total strength `K = Σ_i κ_i`. -/
def totalStrength : ℝ := ∑ i, G.kappa i

theorem totalStrength_nonneg : 0 ≤ G.totalStrength :=
  Finset.sum_nonneg fun i _ => G.kappa_nonneg i

theorem sum_kappa_le_totalStrength (J : Finset ι) : ∑ i ∈ J, G.kappa i ≤ G.totalStrength :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J) fun i _ _ => G.kappa_nonneg i

theorem mem_crosses {Y : Set Λ} {i : ι} : i ∈ G.crosses Y ↔ Crosses (G.supp i : Set Λ) Y := by
  simp [crosses]

/-- An index not crossing `Y` has its support disjoint from `Y` or inside `Y`. -/
theorem disjoint_or_subset_of_not_mem_crosses {Y : Set Λ} {i : ι} (h : i ∉ G.crosses Y) :
    Disjoint (G.supp i : Set Λ) Y ∨ (G.supp i : Set Λ) ⊆ Y := by
  rw [mem_crosses, Crosses, not_and_or, Set.not_nonempty_iff_eq_empty, not_not] at h
  rcases h with h | h
  · exact Or.inl (Set.disjoint_iff_inter_eq_empty.mpr h)
  · exact Or.inr h

/-- M1a, Proposition 3.2: `L_J` is additive over disjoint index sets. -/
theorem subfamily_union [DecidableEq ι] {J J' : Finset ι} (h : Disjoint J J') :
    G.subfamily (J ∪ J') = G.subfamily J + G.subfamily J' :=
  Finset.sum_union h

/-- `L = L^{∂Y} + L'` with `L^{∂Y}` the terms crossing `Y` and `L'` the rest. -/
theorem total_eq_crosses_add_compl [DecidableEq ι] (Y : Set Λ) :
    G.total = G.subfamily (G.crosses Y) + G.subfamily (G.crosses Y)ᶜ := by
  rw [← G.subfamily_union disjoint_compl_right, Finset.union_compl]; rfl

/-- The sub-family generator of `J` applied to the norm of the exponential: (G3) restated. -/
theorem norm_exp_subfamily_le (J : Finset ι) {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • G.subfamily J)‖ ≤ 1 :=
  G.contraction J t ht

/-- (G3) for the full family: `‖e^{tL}‖ ≤ 1`. -/
theorem norm_evolve_le_one {t : ℝ} (ht : 0 ≤ t) : ‖G.evolve t‖ ≤ 1 :=
  G.contraction Finset.univ t ht

/-- M1a, Proposition 3.2: the dynamics does not increase norms, `‖e^{tL} a‖ ≤ ‖a‖`. -/
theorem norm_evolve_le {t : ℝ} (ht : 0 ≤ t) (a : A) : ‖G.evolve t a‖ ≤ ‖a‖ :=
  calc ‖G.evolve t a‖ ≤ ‖G.evolve t‖ * ‖a‖ := (G.evolve t).le_opNorm a
    _ ≤ 1 * ‖a‖ := by gcongr; exact G.norm_evolve_le_one ht
    _ = ‖a‖ := one_mul _

/-- `‖L_J c‖ ≤ Σ_{i ∈ J} κ_i N_{S_i}(c)`, the (G1) bound summed over a sub-family. -/
theorem norm_subfamily_apply_le (J : Finset ι) (c : A) :
    ‖G.subfamily J c‖ ≤ ∑ i ∈ J, G.kappa i * commNorm 𝒜 (↑(G.supp i)) c := by
  unfold subfamily
  rw [_root_.sum_apply]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => G.local_in_arg i c)

end LocalGenerators

end LocalityLean

end
