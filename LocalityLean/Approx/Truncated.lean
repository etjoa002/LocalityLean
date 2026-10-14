/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import LocalityLean.Approx.Twirl
import LocalityLean.Qudit.Bounds

/-!
# Truncated dynamics and approximate locality

On a causal net with local approximation (`LocalApprox`), the evolved observable `A(t)` of
`a ∈ 𝒜(X)` under a family of local generators lies within `2‖a‖ Σ_k ω_k(t)` of the local
algebra of any larger region `X' ⊇ X`, the walk series of the pair `(X'ᶜ, X)` (M3,
Theorem 4.1): the commutator seminorm of `A(t)` with the complement of `X'` is bounded by the
walk form of the path-sum bound, and the local approximation turns the seminorm into a
distance. Under bounded geometry the error is the light-cone tail of M1b.

Hence `e^{tL}` is `ε`-local (M3, Corollary 4.2): with the `r`-neighbourhood map of a bounded
geometry, uniformly with `ε_r(t) = 2|T| (vt)^r e^{vt}/r!`, and exponentially small in `r`.
The qudit net with cyclic alphabets is an instance through its conditional expectation.

## Main definitions

* `LocalityLean.LocalGenerators.truncError`, `LocalityLean.LocalGenerators.neighbourhood`.

## Main statements

* `LocalityLean.LocalGenerators.commNorm_evolve_le`, `norm_sub_P_evolve_le`,
  `norm_sub_P_evolve_le_geom`, `norm_sub_P_evolve_le_cone`, `evolve_isApproxLocalWith`,
  `evolve_isApproxLocalWith_geom`, `evolve_isApproxLocalWith_cone`;
* `LocalityLean.Qudit.QuditInteraction.norm_sub_condExp_evolve_le` and its geometric forms.
-/

noncomputable section

namespace LocalityLean

open LinearAQFT

variable {Λ : Type*} {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [Fintype ι] {𝒜 : Net (Set Λ) A} (G : LocalGenerators ι 𝒜)

namespace LocalGenerators

/-! ### The commutator seminorm of `A(t)` with a disjoint region -/

open Classical in
/-- The walk bound in seminorm form: for `a ∈ 𝒜 X` and `Y` disjoint from `X`,
`N_Y(A(t)) ≤ 2‖a‖ Σ_k ω_k(t)` with the walk terms of the pair `(Y, X)`. -/
theorem commNorm_evolve_le (hc : Net.IsCausal (latticeIndex Λ) 𝒜) (X Y : Set Λ)
    (hXY : Disjoint X Y) {a : A} (ha : a ∈ 𝒜 X) {t : ℝ} (ht : 0 ≤ t) :
    commNorm 𝒜 Y (G.evolve t a) ≤ 2 * ‖a‖ * ∑' k, G.walkTerm X Y t k := by
  refine commNorm_le_of_forall 𝒜 Y fun b hb hb1 => ?_
  have h := G.liebRobinson_walk hc X Y ha hb ht
  have hXY' : ¬ (X ∩ Y).Nonempty := by
    rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty]
    exact hXY
  rw [ite_eq_right hXY', zero_add] at h
  have hS : 0 ≤ ∑' k, G.walkTerm X Y t k := tsum_nonneg fun k => G.walkTerm_nonneg X Y ht k
  calc ‖comm (G.evolve t a) b‖ ≤ 2 * ‖a‖ * ‖b‖ * ∑' k, G.walkTerm X Y t k := h
    _ ≤ 2 * ‖a‖ * 1 * ∑' k, G.walkTerm X Y t k := by
        refine mul_le_mul_of_nonneg_right ?_ hS
        exact mul_le_mul_of_nonneg_left hb1 (by positivity)
    _ = 2 * ‖a‖ * ∑' k, G.walkTerm X Y t k := by ring

/-! ### Truncated dynamics (M3, Theorem 4.1) -/

/-- M3, Theorem 4.1, the walk form: `‖A(t) - P_{X'} A(t)‖ ≤ 2‖a‖ Σ_k ω_k(t)` for `a ∈ 𝒜 X`,
`X ⊆ X'`, with the walk terms of the pair `(X'ᶜ, X)`. -/
theorem norm_sub_P_evolve_le (hc : Net.IsCausal (latticeIndex Λ) 𝒜) (Q : LocalApprox 𝒜)
    {X X' : Set Λ} (hXX' : X ⊆ X') {a : A} (ha : a ∈ 𝒜 X) {t : ℝ} (ht : 0 ≤ t) :
    ‖G.evolve t a - Q.P X' (G.evolve t a)‖ ≤ 2 * ‖a‖ * ∑' k, G.walkTerm X X'ᶜ t k :=
  (Q.norm_sub_P_le X' _).trans
    (G.commNorm_evolve_le hc X X'ᶜ (disjoint_compl_right.mono_left hXX') ha ht)

/-- M3, Theorem 4.1, bounded geometry: if every site of `∂(X'ᶜ)` is farther than `(r - 1)ρ`
from every touched site of `X` (`r ≥ 1`), the error is at most
`2‖a‖ |∂(X'ᶜ)| (vt)^r e^{vt}/r!`. -/
theorem norm_sub_P_evolve_le_geom (hc : Net.IsCausal (latticeIndex Λ) 𝒜) (Q : LocalApprox 𝒜)
    (B : G.BoundedGeometry) {X X' : Set Λ} (hXX' : X ⊆ X') {r : ℕ} (hr : 1 ≤ r)
    (hd : ∀ y ∈ G.boundary X'ᶜ, ∀ x ∈ G.regionSites X, ((r : ℝ) - 1) * B.rho < B.d y x)
    {a : A} (ha : a ∈ 𝒜 X) {t : ℝ} (ht : 0 ≤ t) :
    ‖G.evolve t a - Q.P X' (G.evolve t a)‖ ≤
      2 * ‖a‖ * ((G.boundary X'ᶜ).card *
        ((B.v * t) ^ r / (r.factorial : ℝ) * Real.exp (B.v * t))) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have hd' : ∀ y ∈ G.boundary X'ᶜ, ∀ x ∈ G.regionSites X, (m : ℝ) * B.rho < B.d y x := by
    intro y hy x hx
    have := hd y hy x hx
    push_cast at this
    simpa using this
  refine (G.norm_sub_P_evolve_le hc Q hXX' ha ht).trans ?_
  exact mul_le_mul_of_nonneg_left (B.tsum_walkTerm_le_geom X X'ᶜ hd' ht) (by positivity)

/-- M3, Theorem 4.1, the exponential light cone: under the hypotheses of the geometric form,
for every real `μ` the error is at most `2‖a‖ |∂(X'ᶜ)| e^{vt} e^{-μr} (e^{e^μ vt} - 1)`. -/
theorem norm_sub_P_evolve_le_cone (hc : Net.IsCausal (latticeIndex Λ) 𝒜) (Q : LocalApprox 𝒜)
    (B : G.BoundedGeometry) {X X' : Set Λ} (hXX' : X ⊆ X') {r : ℕ} (hr : 1 ≤ r)
    (hd : ∀ y ∈ G.boundary X'ᶜ, ∀ x ∈ G.regionSites X, ((r : ℝ) - 1) * B.rho < B.d y x)
    (μ : ℝ) {a : A} (ha : a ∈ 𝒜 X) {t : ℝ} (ht : 0 ≤ t) :
    ‖G.evolve t a - Q.P X' (G.evolve t a)‖ ≤
      2 * ‖a‖ * ((G.boundary X'ᶜ).card * (Real.exp (B.v * t) *
        (Real.exp (-μ * r) * (Real.exp (Real.exp μ * (B.v * t)) - 1)))) := by
  refine (G.norm_sub_P_evolve_le_geom hc Q B hXX' hr hd ha ht).trans ?_
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    (by positivity)
  rw [mul_comm (Real.exp (B.v * t))]
  exact mul_le_mul_of_nonneg_right
    (pow_div_factorial_le_exp_sub (mul_nonneg B.v_nonneg ht) μ hr) (Real.exp_pos _).le

/-! ### Approximate locality (M3, Corollary 4.2) -/

/-- The uniform walk error of a neighbourhood map: the largest `2 Σ_k ω_k(t)` over the regions
`O`, for the pairs `((nbhd O)ᶜ, O)`. -/
def truncError (nbhd : Set Λ → Set Λ) (t : ℝ) : ℝ :=
  ⨆ O : Set Λ, 2 * ∑' k, G.walkTerm O (nbhd O)ᶜ t k

/-- M3, Corollary 4.2, general form: `e^{tL}` is `ε(t)`-local with any neighbourhood map
`nbhd` with `O ⊆ nbhd O`, where `ε(t)` is the uniform walk error. -/
theorem evolve_isApproxLocalWith [Finite Λ] (hc : Net.IsCausal (latticeIndex Λ) 𝒜)
    (Q : LocalApprox 𝒜) (nbhd : Set Λ → Set Λ) (hn : ∀ O, O ⊆ nbhd O) {t : ℝ} (ht : 0 ≤ t) :
    IsApproxLocalWith 𝒜 (G.evolve t) nbhd (G.truncError nbhd t) := by
  intro O x hx
  refine ⟨Q.P (nbhd O) (G.evolve t x), Q.P_mem _ _, ?_⟩
  refine (G.norm_sub_P_evolve_le hc Q (hn O) hx ht).trans ?_
  have hle : 2 * ∑' k, G.walkTerm O (nbhd O)ᶜ t k ≤ G.truncError nbhd t := by
    unfold truncError
    exact le_ciSup (Finite.bddAbove_range
      (fun O : Set Λ => 2 * ∑' k, G.walkTerm O (nbhd O)ᶜ t k)) O
  calc 2 * ‖x‖ * ∑' k, G.walkTerm O (nbhd O)ᶜ t k
      = (2 * ∑' k, G.walkTerm O (nbhd O)ᶜ t k) * ‖x‖ := by ring
    _ ≤ G.truncError nbhd t * ‖x‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg _)

/-- The `r`-neighbourhood of a region in a bounded geometry: the sites within distance
`< rρ` of some site of `O`, measured from the site into the region. -/
def neighbourhood (B : G.BoundedGeometry) (r : ℕ) (O : Set Λ) : Set Λ :=
  {w | ∃ x ∈ O, B.d w x < r * B.rho}

theorem subset_neighbourhood (B : G.BoundedGeometry) (hρ : 0 < B.rho) {r : ℕ} (hr : 1 ≤ r)
    (O : Set Λ) : O ⊆ G.neighbourhood B r O := fun x hx => by
  refine ⟨x, hx, ?_⟩
  rw [B.d_self]
  have : (0 : ℝ) < r := by exact_mod_cast hr
  positivity

/-- A site outside the `r`-neighbourhood of `O` is at distance at least `rρ`, hence more than
`(r - 1)ρ`, from every site of `O`. -/
theorem dist_of_not_mem_neighbourhood (B : G.BoundedGeometry) (hρ : 0 < B.rho) {r : ℕ}
    {O : Set Λ} {y : Λ} (hy : y ∉ G.neighbourhood B r O) {x : Λ} (hx : x ∈ O) :
    ((r : ℝ) - 1) * B.rho < B.d y x := by
  have h : (r : ℝ) * B.rho ≤ B.d y x := not_lt.1 fun hlt => hy ⟨x, hx, hlt⟩
  calc ((r : ℝ) - 1) * B.rho < r * B.rho := by rw [sub_mul, one_mul]; linarith
    _ ≤ B.d y x := h

/-- M3, Corollary 4.2, bounded geometry: `e^{tL}` is `ε_r(t)`-local with the
`r`-neighbourhood map, `ε_r(t) = 2|T| (vt)^r e^{vt}/r!` (`ρ > 0`, `r ≥ 1`). -/
theorem evolve_isApproxLocalWith_geom (hc : Net.IsCausal (latticeIndex Λ) 𝒜)
    (Q : LocalApprox 𝒜) (B : G.BoundedGeometry) (hρ : 0 < B.rho) {r : ℕ} (hr : 1 ≤ r) {t : ℝ}
    (ht : 0 ≤ t) :
    IsApproxLocalWith 𝒜 (G.evolve t) (G.neighbourhood B r)
      (2 * G.touched.card * ((B.v * t) ^ r / (r.factorial : ℝ) * Real.exp (B.v * t))) := by
  intro O x hx
  refine ⟨Q.P _ (G.evolve t x), Q.P_mem _ _, ?_⟩
  have hd : ∀ y ∈ G.boundary (G.neighbourhood B r O)ᶜ, ∀ x' ∈ G.regionSites O,
      ((r : ℝ) - 1) * B.rho < B.d y x' := fun y hy x' hx' =>
    G.dist_of_not_mem_neighbourhood B hρ (G.mem_boundary.1 hy).1 (G.mem_regionSites.1 hx').2
  refine (G.norm_sub_P_evolve_le_geom hc Q B (G.subset_neighbourhood B hρ hr O) hr hd hx
    ht).trans ?_
  have hcard : ((G.boundary (G.neighbourhood B r O)ᶜ).card : ℝ) ≤ G.touched.card := by
    exact_mod_cast Finset.card_le_card (G.boundary_subset_touched _)
  have hv : 0 ≤ B.v := B.v_nonneg
  have hg : 0 ≤ (B.v * t) ^ r / (r.factorial : ℝ) * Real.exp (B.v * t) := by positivity
  calc 2 * ‖x‖ * ((G.boundary (G.neighbourhood B r O)ᶜ).card *
        ((B.v * t) ^ r / (r.factorial : ℝ) * Real.exp (B.v * t)))
      ≤ 2 * ‖x‖ * (G.touched.card *
        ((B.v * t) ^ r / (r.factorial : ℝ) * Real.exp (B.v * t))) := by gcongr
    _ = 2 * G.touched.card * ((B.v * t) ^ r / (r.factorial : ℝ) * Real.exp (B.v * t)) * ‖x‖ := by
        ring

/-- M3, Corollary 4.2, the light cone: `e^{tL}` is `ε`-local with the `r`-neighbourhood map
and `ε = 2|T| e^{vt} e^{-μr} (e^{e^μ vt} - 1)`, for every real `μ`. -/
theorem evolve_isApproxLocalWith_cone (hc : Net.IsCausal (latticeIndex Λ) 𝒜)
    (Q : LocalApprox 𝒜) (B : G.BoundedGeometry) (hρ : 0 < B.rho) {r : ℕ} (hr : 1 ≤ r) (μ : ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    IsApproxLocalWith 𝒜 (G.evolve t) (G.neighbourhood B r)
      (2 * G.touched.card * (Real.exp (B.v * t) *
        (Real.exp (-μ * r) * (Real.exp (Real.exp μ * (B.v * t)) - 1)))) := by
  refine (G.evolve_isApproxLocalWith_geom hc Q B hρ hr ht).mono ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [mul_comm (Real.exp (B.v * t))]
  exact mul_le_mul_of_nonneg_right
    (pow_div_factorial_le_exp_sub (mul_nonneg B.v_nonneg ht) μ hr) (Real.exp_pos _).le

end LocalGenerators

/-! ### The qudit instance: Hamiltonian families with the conditional expectation -/

namespace Qudit.QuditInteraction

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {q : Λ → ℕ} [∀ u, NeZero (q u)]
variable {ι : Type*} [Fintype ι] (Φ : QuditInteraction ι fun u => ZMod (q u))

open scoped Matrix.Norms.L2Operator

/-- M3, Theorem 4.1 on the qudit net: `‖A(t) - E_{X'} A(t)‖ ≤ 2‖a‖ Σ_k ω_k(t)`. -/
theorem norm_sub_condExp_evolve_le {X X' : Set Λ} (hXX' : X ⊆ X')
    {a : QuditAlgebra fun u => ZMod (q u)} (ha : a ∈ localAlgebra X) {t : ℝ} (ht : 0 ≤ t) :
    ‖Φ.toGenerators.evolve t a - condExp X' (Φ.toGenerators.evolve t a)‖ ≤
      2 * ‖a‖ * ∑' k, Φ.toGenerators.walkTerm X X'ᶜ t k :=
  Φ.toGenerators.norm_sub_P_evolve_le quditNet_isCausal localApprox hXX' ha ht

/-- M3, Theorem 4.1 on the qudit net, bounded geometry. -/
theorem norm_sub_condExp_evolve_le_geom (B : Φ.toGenerators.BoundedGeometry) {X X' : Set Λ}
    (hXX' : X ⊆ X') {r : ℕ} (hr : 1 ≤ r)
    (hd : ∀ y ∈ Φ.toGenerators.boundary X'ᶜ, ∀ x ∈ Φ.toGenerators.regionSites X,
      ((r : ℝ) - 1) * B.rho < B.d y x)
    {a : QuditAlgebra fun u => ZMod (q u)} (ha : a ∈ localAlgebra X) {t : ℝ} (ht : 0 ≤ t) :
    ‖Φ.toGenerators.evolve t a - condExp X' (Φ.toGenerators.evolve t a)‖ ≤
      2 * ‖a‖ * ((Φ.toGenerators.boundary X'ᶜ).card *
        ((B.v * t) ^ r / (r.factorial : ℝ) * Real.exp (B.v * t))) :=
  Φ.toGenerators.norm_sub_P_evolve_le_geom quditNet_isCausal localApprox B hXX' hr hd ha ht

/-- M3, Theorem 4.1 on the qudit net, the exponential light cone. -/
theorem norm_sub_condExp_evolve_le_cone (B : Φ.toGenerators.BoundedGeometry) {X X' : Set Λ}
    (hXX' : X ⊆ X') {r : ℕ} (hr : 1 ≤ r)
    (hd : ∀ y ∈ Φ.toGenerators.boundary X'ᶜ, ∀ x ∈ Φ.toGenerators.regionSites X,
      ((r : ℝ) - 1) * B.rho < B.d y x) (μ : ℝ)
    {a : QuditAlgebra fun u => ZMod (q u)} (ha : a ∈ localAlgebra X) {t : ℝ} (ht : 0 ≤ t) :
    ‖Φ.toGenerators.evolve t a - condExp X' (Φ.toGenerators.evolve t a)‖ ≤
      2 * ‖a‖ * ((Φ.toGenerators.boundary X'ᶜ).card * (Real.exp (B.v * t) *
        (Real.exp (-μ * r) * (Real.exp (Real.exp μ * (B.v * t)) - 1)))) :=
  Φ.toGenerators.norm_sub_P_evolve_le_cone quditNet_isCausal localApprox B hXX' hr hd μ ha ht

/-- M3, Corollary 4.2 on the qudit net: the Hamiltonian dynamics is an approximate automaton
with the `r`-neighbourhood map. -/
theorem evolve_isApproxLocalWith_geom (B : Φ.toGenerators.BoundedGeometry) (hρ : 0 < B.rho)
    {r : ℕ} (hr : 1 ≤ r) {t : ℝ} (ht : 0 ≤ t) :
    IsApproxLocalWith (quditNet fun u => ZMod (q u)) (Φ.toGenerators.evolve t)
      (Φ.toGenerators.neighbourhood B r)
      (2 * Φ.toGenerators.touched.card *
        ((B.v * t) ^ r / (r.factorial : ℝ) * Real.exp (B.v * t))) :=
  Φ.toGenerators.evolve_isApproxLocalWith_geom quditNet_isCausal localApprox B hρ hr ht

/-- M3, Corollary 4.2 on the qudit net, the light-cone error. -/
theorem evolve_isApproxLocalWith_cone (B : Φ.toGenerators.BoundedGeometry) (hρ : 0 < B.rho)
    {r : ℕ} (hr : 1 ≤ r) (μ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    IsApproxLocalWith (quditNet fun u => ZMod (q u)) (Φ.toGenerators.evolve t)
      (Φ.toGenerators.neighbourhood B r)
      (2 * Φ.toGenerators.touched.card * (Real.exp (B.v * t) *
        (Real.exp (-μ * r) * (Real.exp (Real.exp μ * (B.v * t)) - 1)))) :=
  Φ.toGenerators.evolve_isApproxLocalWith_cone quditNet_isCausal localApprox B hρ hr μ ht

end Qudit.QuditInteraction

end LocalityLean

end
