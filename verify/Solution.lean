/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import LocalityLean

/-!
# The core statements of LocalityLean

This file states, without proofs, the main theorems of LocalityLean on Lieb-Robinson bounds for
quantum lattice systems: nets of local algebras on a lattice and the CCR algebra; families of
local generators with locality in the argument, support closure and contraction; first-contact
paths and the path-sum bound; its closed forms through the site matrix and walks, decay
functions, bounded geometry and the exponential light cone; time reversal; Hamiltonian families;
spin (qudit) lattices and the bounds for spin systems; local approximation, truncated dynamics
and open systems; harmonic bosons and their bounds. A final section gives examples. The
statements use definitions of LocalityLean and of the libraries it builds on (LinearAQFT,
BosonicLean, LocalAlgebrasLean); each is fixed in Mathlib's terms by an entry of this file.

Every statement here is closed by `sorry`. The file `Solution.lean` in this folder repeats each
statement with the identical text and proves it. The tool `lake comparator`, configured by
`comparator.json` in this folder, checks that each theorem named there has exactly the same
statement in both files and that its proof in `Solution.lean` uses no axioms other than
`propext`, `Classical.choice` and `Quot.sound`. The script `check_same_statements.py` checks the
same correspondence on the text of the two files.
-/

open LocalityLean

namespace Sealed

/-! ## Nets of local algebras on a lattice

A net over a preordered set $R$ of regions in a C*-algebra $A$ assigns to each region $O$ a star
subalgebra $\mathcal A(O)$ of $A$. A C*-algebra is a unital complex C*-algebra, and a star
subalgebra is a unital complex star subalgebra. On a lattice with site set $\Lambda$ the regions
are the subsets of $\Lambda$, ordered by inclusion. For elements $a, b$ of $A$,
$[a, b] = ab - ba$. -/

/-- A net over $R$ in a C*-algebra $A$ assigns to each region $O$ a star subalgebra
$\mathcal A(O)$ of $A$; an assignment $O \mapsto F(O)$ is a net exactly when it is monotone
($O \le O'$ implies $F(O) \subseteq F(O')$, isotony) and every $F(O)$ is norm-closed. -/
theorem net_iff {R : Type*} [Preorder R] {A : Type*} [CStarAlgebra A]
    (F : R → StarSubalgebra ℂ A) :
    (∃ 𝒜 : LinearAQFT.Net R A, ∀ O, 𝒜 O = F O) ↔ Monotone F ∧ ∀ O, IsClosed (F O : Set A) := by
  constructor
  · rintro ⟨𝒜, h⟩
    refine ⟨fun O O' hO => ?_, fun O => ?_⟩
    · rw [← h, ← h]; exact 𝒜.mono hO
    · rw [← h]; exact 𝒜.isClosed O
  · rintro ⟨hm, hc⟩
    exact ⟨⟨⟨F, hm⟩, hc⟩, fun _ => rfl⟩

/-- The lattice causal index on the subsets of a site set $\Lambda$: two regions are orthogonal
exactly when they are disjoint, and a region depends on another exactly when it is contained in
it. A net $\mathcal A$ is causal for this index exactly when elements of the algebras of
disjoint regions commute: $X \cap Y = \emptyset$, $a \in \mathcal A(X)$ and
$b \in \mathcal A(Y)$ give $ab = ba$. -/
theorem lattice_index {Λ : Type*} {A : Type*} [CStarAlgebra A]
    (𝒜 : LinearAQFT.Net (Set Λ) A) :
    (∀ X Y : Set Λ, (latticeIndex Λ).Orthogonal X Y ↔ Disjoint X Y) ∧
    (∀ X Y : Set Λ, (latticeIndex Λ).Dependent X Y ↔ X ⊆ Y) ∧
    (LinearAQFT.Net.IsCausal (latticeIndex Λ) 𝒜 ↔
      ∀ X Y : Set Λ, Disjoint X Y → ∀ a ∈ 𝒜 X, ∀ b ∈ 𝒜 Y, Commute a b) :=
  ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl,
    ⟨fun h X Y => @h X Y, fun h X Y => h X Y⟩⟩

/-- The commutator seminorm of a region. For a net $\mathcal A$ on the subsets of $\Lambda$, a
region $S$ and $c \in A$, $N_S(c) = \sup \{\|[c, b]\| : b \in \mathcal A(S), \|b\| \le 1\}$;
this supremum is finite, with $0 \le N_S(c) \le 2\|c\|$ and $\|[c, b]\| \le N_S(c)$ for every
$b$ in the unit ball of $\mathcal A(S)$. A set $S$ crosses a region $Y$ when it meets $Y$ and is
not contained in $Y$. -/
theorem commutator_seminorm {Λ : Type*} {A : Type*} [CStarAlgebra A]
    (𝒜 : LinearAQFT.Net (Set Λ) A) (S Y : Set Λ) (a b c : A) :
    comm a b = a * b - b * a ∧
    commNorm 𝒜 S c = sSup ((fun b => ‖c * b - b * c‖) '' {b | b ∈ 𝒜 S ∧ ‖b‖ ≤ 1}) ∧
    0 ≤ commNorm 𝒜 S c ∧ commNorm 𝒜 S c ≤ 2 * ‖c‖ ∧
    (∀ b ∈ 𝒜 S, ‖b‖ ≤ 1 → ‖c * b - b * c‖ ≤ commNorm 𝒜 S c) ∧
    (Crosses S Y ↔ (S ∩ Y).Nonempty ∧ ¬ S ⊆ Y) :=
  ⟨rfl, rfl, commNorm_nonneg 𝒜 S c, commNorm_le_two_mul_norm 𝒜 S c,
    fun _ hb hb1 => norm_comm_le_commNorm 𝒜 S hb hb1, Iff.rfl⟩

/-! ## The CCR algebra

Let $V$ be a real vector space and $\sigma$ a real bilinear form on $V$. The Hilbert space
$\ell^2(V)$ consists of the square-summable complex functions on the set $V$. A bilinear form is
alternating when $\sigma(u, u) = 0$ for every $u$. -/

open BosonicLean.Weyl in
/-- The Weyl operators and the CCR algebra: for $u \in V$ the Weyl operator $W(u)$ is the
bounded operator on $\ell^2(V)$ with $(W(u) f)(v) = e^{i\sigma(u, v)/2} f(v + u)$; the CCR
algebra $\mathrm{CCR}(V, \sigma)$ is the norm closure of the star subalgebra generated by the
Weyl operators, a C*-algebra; and $W(u)$, regarded as an element of $\mathrm{CCR}(V, \sigma)$,
is the same operator. -/
theorem weyl_and_CCR {V : Type*} [AddCommGroup V] [Module ℝ V] (σ : LinearMap.BilinForm ℝ V) :
    (∀ (u : V) (f : lp (fun _ : V => ℂ) 2) (v : V),
      weyl σ u f v = Complex.exp (((σ u v / 2 : ℝ) : ℂ) * Complex.I) * f (v + u)) ∧
    CCR σ = (StarAlgebra.adjoin ℂ (Set.range (weyl σ))).topologicalClosure ∧
    ∀ u : V, ((wCCR σ u : CCR σ) : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2) =
      weyl σ u :=
  ⟨fun u f v => weyl_apply σ u f v, rfl, fun _ => rfl⟩

open BosonicLean.Weyl in
/-- For alternating $\sigma$ every Weyl operator is unitary, $W(u)^* = W(-u)$, and the Weyl
relation $W(u) W(w) = e^{-i\sigma(u, w)/2} W(u + w)$ holds. -/
theorem weyl_relations {V : Type*} [AddCommGroup V] [Module ℝ V]
    {σ : LinearMap.BilinForm ℝ V} (hσ : σ.IsAlt) :
    (∀ u, weyl σ u ∈ unitary (lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2)) ∧
    (∀ u, star (weyl σ u) = weyl σ (-u)) ∧
    ∀ u w, weyl σ u * weyl σ w =
      Complex.exp (((-(σ u w) / 2 : ℝ) : ℂ) * Complex.I) • weyl σ (u + w) :=
  ⟨weyl_mem_unitary σ hσ, star_weyl σ hσ, weyl_mul σ hσ⟩

/-! ## Local generators

A family of local generators on a net $\mathcal A$ is indexed by a finite type $\iota$; its
$i$-th term has a finite support $S_i \subseteq \Lambda$, a bounded complex-linear map
$L_i : A \to A$ and a strength $\kappa_i$. The norm of a bounded linear map of $A$ is the
operator norm, and $e^{T}$ is the exponential series of a bounded linear map $T$. -/

/-- A family of local generators: given finite supports $S_i$, bounded linear maps
$L_i : A \to A$ and reals $\kappa_i$ for $i \in \iota$, there is a family of local generators on
$\mathcal A$ with these data exactly when (i) $\kappa_i \ge 0$; (G1) locality in the argument,
$\|L_i c\| \le \kappa_i N_{S_i}(c)$ for every $c \in A$; (G2) support closure,
$L_i(\mathcal A(Z)) \subseteq \mathcal A(Z \cup S_i)$ for every region $Z$; (G3) contraction,
$\|e^{t L_J}\| \le 1$ for every finite set $J$ of indices and every $t \ge 0$, where
$L_J = \sum_{i \in J} L_i$. The family is determined by its data. -/
theorem local_generators_iff {Λ : Type*} {A : Type*} [CStarAlgebra A] {ι : Type*} [Fintype ι]
    (𝒜 : LinearAQFT.Net (Set Λ) A) (s : ι → Finset Λ) (L : ι → (A →L[ℂ] A)) (κ : ι → ℝ) :
    ((∃ G : LocalGenerators ι 𝒜, G.supp = s ∧ G.L = L ∧ G.kappa = κ) ↔
      (∀ i, 0 ≤ κ i) ∧ (∀ i c, ‖L i c‖ ≤ κ i * commNorm 𝒜 (s i : Set Λ) c) ∧
      (∀ i (Z : Set Λ), ∀ a ∈ 𝒜 Z, L i a ∈ 𝒜 (Z ∪ (s i : Set Λ))) ∧
      ∀ (J : Finset ι) (t : ℝ), 0 ≤ t → ‖NormedSpace.exp (t • ∑ i ∈ J, L i)‖ ≤ 1) ∧
    ∀ G G' : LocalGenerators ι 𝒜, G.supp = G'.supp → G.L = G'.L → G.kappa = G'.kappa →
      G = G' := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨G, rfl, rfl, rfl⟩
    exact ⟨G.kappa_nonneg, G.local_in_arg, G.maps_into, G.contraction⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨s, L, κ, h1, h2, h3, h4⟩, rfl, rfl, rfl⟩
  · rintro ⟨s, L, κ, _, _, _, _⟩ ⟨s', L', κ', _, _, _, _⟩ hs hL hκ
    cases hs; cases hL; cases hκ
    rfl

/-- The data derived from a family of local generators: the generator of a finite set $J$ of
indices is $L_J = \sum_{i \in J} L_i$, the full generator is $L = \sum_i L_i$, the dynamics is
$t \mapsto e^{tL}$, the indices crossing a region $Y$ are those $i$ with $S_i$ crossing $Y$, and
the total strength is $K = \sum_i \kappa_i$. The dynamics does not increase norms:
$\|e^{tL} a\| \le \|a\|$ for $t \ge 0$. -/
theorem generator_data {Λ : Type*} {A : Type*} [CStarAlgebra A] {ι : Type*} [Fintype ι]
    {𝒜 : LinearAQFT.Net (Set Λ) A} (G : LocalGenerators ι 𝒜) :
    (∀ J : Finset ι, G.subfamily J = ∑ i ∈ J, G.L i) ∧ G.total = ∑ i, G.L i ∧
    (∀ t : ℝ, G.evolve t = NormedSpace.exp (t • ∑ i, G.L i)) ∧
    (∀ (Y : Set Λ) (i : ι), i ∈ G.crosses Y ↔ Crosses (G.supp i : Set Λ) Y) ∧
    G.totalStrength = ∑ i, G.kappa i ∧
    ∀ t : ℝ, 0 ≤ t → ∀ a, ‖G.evolve t a‖ ≤ ‖a‖ :=
  ⟨fun _ => rfl, rfl, fun _ => rfl, fun _ _ => G.mem_crosses, rfl,
    fun _ ht a => G.norm_evolve_le ht a⟩

/-! ## Paths and the path-sum bound

Let $X$ be the region of an observable and $Y$ the region of a probe. The first-contact paths of
length $k$ from $Y$ to $X$ are sequences of indices $i_1, \dots, i_k$; their weighted count
$P_k(Y, X)$ enters the path-sum bound. For a proposition $p$, $[p]$ is $1$ if $p$ holds and $0$
otherwise. -/

/-- First-contact paths. There is no path of length $0$. A sequence $i_1, \dots, i_{k+1}$ of
indices is a first-contact path from $Y$ to $X$ exactly when $S_{i_1}$ crosses $Y$, each
$S_{i_{j+1}}$ crosses $S_{i_j}$ ($1 \le j \le k$), the supports $S_{i_1}, \dots, S_{i_k}$ are
disjoint from $X$, and $S_{i_{k+1}}$ meets $X$. -/
theorem first_contact_path {Λ : Type*} {A : Type*} [CStarAlgebra A] {ι : Type*} [Fintype ι]
    {𝒜 : LinearAQFT.Net (Set Λ) A} (G : LocalGenerators ι 𝒜) (X Y : Set Λ) :
    (∀ p : Fin 0 → ι, ¬ G.IsPath X Y p) ∧
    ∀ (k : ℕ) (p : Fin (k + 1) → ι), G.IsPath X Y p ↔
      Crosses (G.supp (p 0) : Set Λ) Y ∧
      (∀ j : Fin k, Crosses (G.supp (p j.succ) : Set Λ) (G.supp (p j.castSucc) : Set Λ)) ∧
      (∀ j : Fin k, Disjoint (G.supp (p j.castSucc) : Set Λ) X) ∧
      ((G.supp (p (Fin.last k)) : Set Λ) ∩ X).Nonempty :=
  ⟨fun _ h => h, fun _ _ => Iff.rfl⟩

open Classical in
/-- The weighted path count. $P_k(Y, X) = \sum \kappa_{i_1} \cdots \kappa_{i_k}$, the sum over
the first-contact paths $i_1, \dots, i_k$ of length $k$ from $Y$ to $X$. It satisfies the
recursion $P_1(Y, X) = \sum \kappa_i$ over the indices $i$ with $S_i$ crossing $Y$ and meeting
$X$, and $P_{k+2}(Y, X) = \sum \kappa_i P_{k+1}(S_i, X)$ over the indices $i$ with $S_i$
crossing $Y$ and disjoint from $X$; here the second form of the count, defined by this
recursion with value $0$ at length $0$, agrees with the first at every length $k \ge 1$. Every
count is at most $K^k$, $K = \sum_i \kappa_i$. -/
theorem path_count {Λ : Type*} {A : Type*} [CStarAlgebra A] {ι : Type*} [Fintype ι]
    {𝒜 : LinearAQFT.Net (Set Λ) A} (G : LocalGenerators ι 𝒜) (X Y : Set Λ) :
    (∀ k : ℕ, G.pathSum X Y k =
      ∑ p ∈ (Finset.univ : Finset (Fin k → ι)).filter (G.IsPath X Y), ∏ j, G.kappa (p j)) ∧
    (∀ k : ℕ, G.pathSum X Y (k + 1) = G.pathSumRec X (k + 1) Y) ∧
    (∀ Z : Set Λ, G.pathSumRec X 0 Z = 0) ∧
    (∀ Z : Set Λ, G.pathSumRec X 1 Z = ∑ i ∈ G.bridge X Z, G.kappa i) ∧
    (∀ (k : ℕ) (Z : Set Λ), G.pathSumRec X (k + 2) Z =
      ∑ i ∈ G.through X Z, G.kappa i * G.pathSumRec X (k + 1) (G.supp i)) ∧
    (∀ (Z : Set Λ) (i : ι), i ∈ G.bridge X Z ↔
      Crosses (G.supp i : Set Λ) Z ∧ ((G.supp i : Set Λ) ∩ X).Nonempty) ∧
    (∀ (Z : Set Λ) (i : ι), i ∈ G.through X Z ↔
      Crosses (G.supp i : Set Λ) Z ∧ Disjoint (G.supp i : Set Λ) X) ∧
    ∀ (k : ℕ) (Z : Set Λ), G.pathSumRec X k Z ≤ G.totalStrength ^ k :=
  ⟨fun _ => rfl, fun k => G.pathSum_eq_pathSumRec X Y k, fun Z => G.pathSumRec_zero X Z,
    fun Z => G.pathSumRec_one X Z, fun k Z => G.pathSumRec_succ_succ X Z k,
    fun _ _ => G.mem_bridge, fun _ _ => G.mem_through, fun k Z => G.pathSumRec_le X k Z⟩

/-- The terms of the series. The coefficient is $c_k(t) = (2t)^{k+1}/(k+1)!$; the $k$-th term of
the path series is $c_k(t) P_{k+1}(Y, X)$. The commutator bound
$C_{X,Y}(t)$ is the supremum of $\|[e^{tL} a, b]\|$ over $a$ in the unit ball of
$\mathcal A(X)$ and $b$ in the unit ball of $\mathcal A(Y)$. -/
theorem series_terms {Λ : Type*} {A : Type*} [CStarAlgebra A] {ι : Type*} [Fintype ι]
    {𝒜 : LinearAQFT.Net (Set Λ) A} (G : LocalGenerators ι 𝒜) (X Y : Set Λ) (t : ℝ) :
    (∀ k : ℕ, LocalGenerators.coef k t = (2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ)) ∧
    (∀ k : ℕ, G.seriesTerm X Y t k = LocalGenerators.coef k t * G.pathSum X Y (k + 1)) ∧
    G.commBound X Y t = sSup ((fun p : A × A => ‖comm (G.evolve t p.1) p.2‖) ''
      {p | p.1 ∈ 𝒜 X ∧ ‖p.1‖ ≤ 1 ∧ p.2 ∈ 𝒜 Y ∧ ‖p.2‖ ≤ 1}) := by
  refine ⟨fun _ => rfl, fun k => ?_, rfl⟩
  rw [LocalGenerators.seriesTerm, G.pathSum_eq_pathSumRec]

open Classical in
/-- The path-sum bound. Let $\mathcal A$ be a net on the subsets of $\Lambda$ that is causal for
the lattice index, $(S_i, L_i, \kappa_i)$ a family of local generators with $L = \sum_i L_i$,
$a \in \mathcal A(X)$, $b \in \mathcal A(Y)$ and $t \ge 0$. Then the path series
$\sum_{k \ge 1} \frac{(2t)^k}{k!} P_k(Y, X)$ converges and
$\|[e^{tL} a, b]\| \le 2\|a\|\|b\| \bigl([X \cap Y \ne \emptyset] + \sum_{k \ge 1}
\frac{(2t)^k}{k!} P_k(Y, X)\bigr)$. -/
theorem path_sum_bound {Λ : Type*} {A : Type*} [CStarAlgebra A] {ι : Type*} [Fintype ι]
    {𝒜 : LinearAQFT.Net (Set Λ) A} (G : LocalGenerators ι 𝒜)
    (hc : LinearAQFT.Net.IsCausal (latticeIndex Λ) 𝒜) (X Y : Set Λ) {a b : A} (ha : a ∈ 𝒜 X)
    (hb : b ∈ 𝒜 Y) {t : ℝ} (ht : 0 ≤ t) :
    Summable (fun k : ℕ => (2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ) * G.pathSum X Y (k + 1)) ∧
    ‖comm (G.evolve t a) b‖ ≤ 2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
      ∑' k : ℕ, (2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ) * G.pathSum X Y (k + 1)) := by
  have h : (fun k : ℕ => (2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ) * G.pathSum X Y (k + 1)) =
      G.seriesTerm X Y t := funext fun k => by
    rw [LocalGenerators.seriesTerm, LocalGenerators.coef, G.pathSum_eq_pathSumRec]
  rw [h]
  exact ⟨G.summable_seriesTerm X Y ht, G.liebRobinson hc X Y ha hb ht⟩

open Classical in
/-- The path-sum bound in supremum form: under the hypotheses of the path-sum bound, the
commutator bound satisfies $C_{X,Y}(t) \le 2 \bigl([X \cap Y \ne \emptyset] + \sum_{k \ge 1}
\frac{(2t)^k}{k!} P_k(Y, X)\bigr)$; the series converges by the path-sum bound. -/
theorem sup_bound {Λ : Type*} {A : Type*} [CStarAlgebra A] {ι : Type*} [Fintype ι]
    {𝒜 : LinearAQFT.Net (Set Λ) A} (G : LocalGenerators ι 𝒜)
    (hc : LinearAQFT.Net.IsCausal (latticeIndex Λ) 𝒜) (X Y : Set Λ) {t : ℝ} (ht : 0 ≤ t) :
    G.commBound X Y t ≤ 2 * ((if (X ∩ Y).Nonempty then 1 else 0) +
      ∑' k : ℕ, (2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ) * G.pathSum X Y (k + 1)) := by
  have h : (fun k : ℕ => (2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ) * G.pathSum X Y (k + 1)) =
      G.seriesTerm X Y t := funext fun k => by
    rw [LocalGenerators.seriesTerm, LocalGenerators.coef, G.pathSum_eq_pathSumRec]
  rw [h]
  exact G.commBound_le hc X Y ht

/-! ## Closed forms: the site matrix and walks

The touched sites are $T = \bigcup_i S_i$, a finite set. The site matrix
$h_{uv} = \sum_{i : u, v \in S_i} \kappa_i$ is a function on pairs of sites. The boundary of a
region $Y$ is the set $\partial Y$ of sites of $Y$ that lie in the support of an index crossing
$Y$. -/

open Classical in
/-- The site matrix and walk weights. The touched sites are $T = \bigcup_i S_i$, and
$h_{uv} = \sum_i \kappa_i [u \in S_i][v \in S_i]$. The walk weights are $w_0(y, x) = [y = x]$
and $w_{k+1}(y, x) = \sum_{z \in T} h_{yz} w_k(z, x)$. The boundary $\partial Y$ consists of
the sites $y \in Y$ with $y \in S_i$ for some $i$ with $S_i$ crossing $Y$, and the touched
sites of $X$ are $X \cap T$. The walk sum is
$W_k(Y, X) = \sum_{y \in \partial Y} \sum_{x \in X \cap T} w_k(y, x)$, and the $k$-th term of
the walk series is $\frac{(2t)^{k+1}}{(k+1)!} W_{k+1}(Y, X)$. -/
theorem site_matrix_walks {Λ : Type*} {A : Type*} [CStarAlgebra A] {ι : Type*} [Fintype ι]
    {𝒜 : LinearAQFT.Net (Set Λ) A} (G : LocalGenerators ι 𝒜) :
    G.touched = Finset.univ.biUnion G.supp ∧
    (∀ u v : Λ, G.siteMatrix u v = ∑ i, G.kappa i * (if u ∈ G.supp i then 1 else 0) *
      (if v ∈ G.supp i then 1 else 0)) ∧
    (∀ y x : Λ, G.walk 0 y x = if y = x then 1 else 0) ∧
    (∀ (k : ℕ) (y x : Λ), G.walk (k + 1) y x = ∑ z ∈ G.touched, G.siteMatrix y z * G.walk k z x) ∧
    (∀ (Y : Set Λ) (y : Λ), y ∈ G.boundary Y ↔
      y ∈ Y ∧ ∃ i, Crosses (G.supp i : Set Λ) Y ∧ y ∈ G.supp i) ∧
    (∀ (X : Set Λ) (x : Λ), x ∈ G.regionSites X ↔ (∃ i, x ∈ G.supp i) ∧ x ∈ X) ∧
    (∀ (X Y : Set Λ) (k : ℕ),
      G.walkSum X Y k = ∑ y ∈ G.boundary Y, ∑ x ∈ G.regionSites X, G.walk k y x) ∧
    ∀ (X Y : Set Λ) (t : ℝ) (k : ℕ),
      G.walkTerm X Y t k = (2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ) * G.walkSum X Y (k + 1) := by
  refine ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, fun k y x => G.walk_succ k y x, fun Y y => ?_,
    fun X x => ?_, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  · rw [G.mem_boundary]
    simp only [G.mem_crosses]
  · rw [G.mem_regionSites, G.mem_touched]

open Classical in
/-- The walk bound. Under the hypotheses of the path-sum bound, the path count is dominated by
the walk sum, $P_{k+1}(Y, X) \le W_{k+1}(Y, X)$ for every $k \ge 0$; the walk series
$\sum_{k \ge 1} \frac{(2t)^k}{k!} W_k(Y, X)$ converges; and
$\|[e^{tL} a, b]\| \le 2\|a\|\|b\| \bigl([X \cap Y \ne \emptyset] + \sum_{k \ge 1}
\frac{(2t)^k}{k!} W_k(Y, X)\bigr)$. -/
theorem walk_bound {Λ : Type*} {A : Type*} [CStarAlgebra A] {ι : Type*} [Fintype ι]
    {𝒜 : LinearAQFT.Net (Set Λ) A} (G : LocalGenerators ι 𝒜)
    (hc : LinearAQFT.Net.IsCausal (latticeIndex Λ) 𝒜) (X Y : Set Λ) {a b : A} (ha : a ∈ 𝒜 X)
    (hb : b ∈ 𝒜 Y) {t : ℝ} (ht : 0 ≤ t) :
    (∀ k : ℕ, G.pathSum X Y (k + 1) ≤ G.walkSum X Y (k + 1)) ∧
    Summable (fun k : ℕ => (2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ) * G.walkSum X Y (k + 1)) ∧
    ‖comm (G.evolve t a) b‖ ≤ 2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
      ∑' k : ℕ, (2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ) * G.walkSum X Y (k + 1)) := by
  refine ⟨fun k => ?_, G.summable_walkTerm X Y ht, G.liebRobinson_walk hc X Y ha hb ht⟩
  rw [G.pathSum_eq_pathSumRec]
  exact G.pathSumRec_le_walkSum X (k + 1) (Nat.succ_pos k) Y

open Classical in
/-- The walk bound on a finite lattice. If the site set $\Lambda$ is finite, the walk weights are
the entries of the powers of the site matrix, $w_k(y, x) = (h^k)_{yx}$, and under the
hypotheses of the path-sum bound
$\|[e^{tL} a, b]\| \le 2\|a\|\|b\| \bigl([X \cap Y \ne \emptyset] + \sum_{y \in \partial Y}
\sum_{x \in X \cap T} (e^{2th} - 1)_{yx}\bigr)$, with $e^{2th}$ the matrix exponential and $1$
the identity matrix. -/
theorem matrix_exponential_bound {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {A : Type*}
    [CStarAlgebra A] {ι : Type*} [Fintype ι] {𝒜 : LinearAQFT.Net (Set Λ) A}
    (G : LocalGenerators ι 𝒜) (hc : LinearAQFT.Net.IsCausal (latticeIndex Λ) 𝒜) (X Y : Set Λ)
    {a b : A} (ha : a ∈ 𝒜 X) (hb : b ∈ 𝒜 Y) {t : ℝ} (ht : 0 ≤ t) :
    (∀ (k : ℕ) (y x : Λ), G.walk k y x = ((Matrix.of fun u v => G.siteMatrix u v) ^ k) y x) ∧
    ‖comm (G.evolve t a) b‖ ≤ 2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
      ∑ y ∈ G.boundary Y, ∑ x ∈ G.regionSites X,
        (NormedSpace.exp ((2 * t) • Matrix.of fun u v => G.siteMatrix u v) y x -
          (1 : Matrix Λ Λ ℝ) y x)) :=
  ⟨G.walk_eq_pow_apply, G.liebRobinson_matrixExp hc X Y ha hb ht⟩

/-! ## Closed forms: decay functions and bounded geometry -/

/-- Decay kernels. Given $F : \Lambda \times \Lambda \to \mathbb R$ and $C \in \mathbb R$,
there is a decay kernel with function $F$ and reproducing constant $C_F = C$ exactly when
$C > 0$, $F \ge 0$, and $\sum_{z \in T'} F(x, z) F(z, y) \le C F(x, y)$ for all sites $x, y$ and
every finite set $T'$ of sites. The kernel is determined by $F$ and $C$. -/
theorem decay_kernel_iff {Λ : Type*} (F : Λ → Λ → ℝ) (C : ℝ) :
    ((∃ K : DecayKernel Λ, K.F = F ∧ K.CF = C) ↔
      0 < C ∧ (∀ x y, 0 ≤ F x y) ∧
      ∀ (x y : Λ) (T' : Finset Λ), ∑ z ∈ T', F x z * F z y ≤ C * F x y) ∧
    ∀ K K' : DecayKernel Λ, K.F = K'.F → K.CF = K'.CF → K = K' := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨K, rfl, rfl⟩
    exact ⟨K.CF_pos, K.F_nonneg, K.reproducing⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨F, C, h1, h2, h3⟩, rfl, rfl⟩
  · rintro ⟨F, C, _, _, _⟩ ⟨F', C', _, _, _⟩ hF hC
    cases hF; cases hC
    rfl

open Classical in
/-- The decay-function bound. A real $N$ is an $F$-bound of the family when $N \ge 0$ and
$h_{xy} \le N F(x, y)$ for all sites $x, y$; the kernel sum is
$\Sigma_F(Y, X) = \sum_{y \in \partial Y} \sum_{x \in X \cap T} F(y, x)$. If $N$ is an $F$-bound,
then under the hypotheses of the path-sum bound
$\|[e^{tL} a, b]\| \le 2\|a\|\|b\| \bigl([X \cap Y \ne \emptyset] +
\frac{e^{2 N C_F t} - 1}{C_F} \Sigma_F(Y, X)\bigr)$. -/
theorem decay_bound {Λ : Type*} {A : Type*} [CStarAlgebra A] {ι : Type*} [Fintype ι]
    {𝒜 : LinearAQFT.Net (Set Λ) A} (G : LocalGenerators ι 𝒜) (K : DecayKernel Λ) (N : ℝ)
    (X Y : Set Λ) :
    (G.IsFBound K N ↔ 0 ≤ N ∧ ∀ x y, G.siteMatrix x y ≤ N * K.F x y) ∧
    G.kernelSum K X Y = ∑ y ∈ G.boundary Y, ∑ x ∈ G.regionSites X, K.F y x ∧
    (LinearAQFT.Net.IsCausal (latticeIndex Λ) 𝒜 → G.IsFBound K N →
      ∀ a ∈ 𝒜 X, ∀ b ∈ 𝒜 Y, ∀ t : ℝ, 0 ≤ t →
        ‖comm (G.evolve t a) b‖ ≤ 2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
          (Real.exp (2 * N * K.CF * t) - 1) / K.CF * G.kernelSum K X Y)) :=
  ⟨Iff.rfl, rfl, fun hc hN _ ha _ hb _ ht => G.liebRobinson_decay hc K hN X Y ha hb ht⟩

open Classical in
/-- Bounded geometry. Given $d : \Lambda \times \Lambda \to \mathbb R$, natural numbers $g, R$
and reals $\ell, \rho$, the family has bounded geometry with these data exactly when
$d(u, u) = 0$, $d(u, w) \le d(u, v) + d(v, w)$, $\ell \ge 0$, $\rho \ge 0$, every site lies in
the supports $S_i$ of at most $g$ indices $i$, every strength is at most $\ell$, every
support has at most $R$ sites,
and $d(u, v) \le \rho$ for all $u, v$ in a common support. The bounded geometry is determined
by these data; its row-sum bound is $M = g \ell R$ and its velocity $v = 2 g \ell R$. -/
theorem bounded_geometry_iff {Λ : Type*} {A : Type*} [CStarAlgebra A] {ι : Type*} [Fintype ι]
    {𝒜 : LinearAQFT.Net (Set Λ) A} (G : LocalGenerators ι 𝒜) (d : Λ → Λ → ℝ) (g : ℕ) (ℓ : ℝ)
    (R : ℕ) (ρ : ℝ) :
    ((∃ B : G.BoundedGeometry, B.d = d ∧ B.g = g ∧ B.ell = ℓ ∧ B.R = R ∧ B.rho = ρ) ↔
      (∀ u, d u u = 0) ∧ (∀ u v w, d u w ≤ d u v + d v w) ∧ 0 ≤ ℓ ∧ 0 ≤ ρ ∧
      (∀ u, (Finset.univ.filter fun i => u ∈ G.supp i).card ≤ g) ∧ (∀ i, G.kappa i ≤ ℓ) ∧
      (∀ i, (G.supp i).card ≤ R) ∧ ∀ i, ∀ u ∈ G.supp i, ∀ v ∈ G.supp i, d u v ≤ ρ) ∧
    (∀ B B' : G.BoundedGeometry, B.d = B'.d → B.g = B'.g → B.ell = B'.ell → B.R = B'.R →
      B.rho = B'.rho → B = B') ∧
    ∀ B : G.BoundedGeometry, B.M = B.g * B.ell * B.R ∧ B.v = 2 * B.g * B.ell * B.R := by
  refine ⟨⟨?_, ?_⟩, ?_, fun B => ⟨rfl, ?_⟩⟩
  · rintro ⟨B, rfl, rfl, rfl, rfl, rfl⟩
    exact ⟨B.d_self, B.d_triangle, B.ell_nonneg, B.rho_nonneg, B.degree, B.strength, B.size,
      B.diam⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨⟨d, h1, h2, g, ℓ, h3, R, ρ, h4, h5, h6, h7, h8⟩, rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨d, _, _, g, ℓ, _, R, ρ, _, _, _, _, _⟩ ⟨d', _, _, g', ℓ', _, R', ρ', _, _, _, _, _⟩
      hd hg hℓ hR hρ
    cases hd; cases hg; cases hℓ; cases hR; cases hρ
    rfl
  · simp only [LocalGenerators.BoundedGeometry.v, LocalGenerators.BoundedGeometry.M]
    ring

open Classical in
/-- The bound under bounded geometry and the exponential light cone. Let the family have
bounded geometry with distance $d$, diameter bound $\rho$ and velocity $v = 2 g \ell R$, let
$r \ge 1$ be an integer, and let $d(y, x) > (r - 1)\rho$ for every $y \in \partial Y$ and every
$x \in X \cap T$. Under the hypotheses of the path-sum bound,
$\|[e^{tL} a, b]\| \le 2\|a\|\|b\| \bigl([X \cap Y \ne \emptyset] +
|\partial Y| \frac{(vt)^r}{r!} e^{vt}\bigr)$, and for every real $\mu$,
$\|[e^{tL} a, b]\| \le 2\|a\|\|b\| \bigl([X \cap Y \ne \emptyset] +
|\partial Y| e^{vt} e^{-\mu r} (e^{e^{\mu} v t} - 1)\bigr)$. -/
theorem light_cone_bound {Λ : Type*} {A : Type*} [CStarAlgebra A] {ι : Type*} [Fintype ι]
    {𝒜 : LinearAQFT.Net (Set Λ) A} (G : LocalGenerators ι 𝒜)
    (hc : LinearAQFT.Net.IsCausal (latticeIndex Λ) 𝒜) (B : G.BoundedGeometry) (X Y : Set Λ)
    {r : ℕ} (hr : 1 ≤ r)
    (hd : ∀ y ∈ G.boundary Y, ∀ x ∈ G.regionSites X, ((r : ℝ) - 1) * B.rho < B.d y x)
    {a b : A} (ha : a ∈ 𝒜 X) (hb : b ∈ 𝒜 Y) {t : ℝ} (ht : 0 ≤ t) :
    ‖comm (G.evolve t a) b‖ ≤ 2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
      (G.boundary Y).card * ((B.v * t) ^ r / (r.factorial : ℝ) * Real.exp (B.v * t))) ∧
    ∀ μ : ℝ, ‖comm (G.evolve t a) b‖ ≤ 2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
      (G.boundary Y).card * (Real.exp (B.v * t) *
        (Real.exp (-μ * r) * (Real.exp (Real.exp μ * (B.v * t)) - 1)))) :=
  ⟨G.liebRobinson_boundedGeometry hc B X Y hr hd ha hb ht,
    fun μ => G.liebRobinson_cone hc B X Y hr hd μ ha hb ht⟩

/-! ## Time reversal and the graded bracket -/

/-- The negated family. The family is negation-contractive when $\|e^{-t L_J}\| \le 1$ for every
finite set $J$ of indices and every $t \ge 0$. Then the negated family, with the same supports
and strengths and the generators $-L_i$, is a family of local generators, and its dynamics is
the dynamics of the family run backwards: $e^{t(-L)} = e^{-tL}$. -/
theorem negated_family {Λ : Type*} {A : Type*} [CStarAlgebra A] {ι : Type*} [Fintype ι]
    {𝒜 : LinearAQFT.Net (Set Λ) A} (G : LocalGenerators ι 𝒜) :
    (G.NegContractive ↔
      ∀ (J : Finset ι) (t : ℝ), 0 ≤ t → ‖NormedSpace.exp (t • ∑ i ∈ J, -G.L i)‖ ≤ 1) ∧
    ∀ h : G.NegContractive, (G.neg h).supp = G.supp ∧ (G.neg h).L = (fun i => -G.L i) ∧
      (G.neg h).kappa = G.kappa ∧ ∀ t : ℝ, (G.neg h).evolve t = G.evolve (-t) :=
  ⟨Iff.rfl, fun h => ⟨rfl, rfl, rfl, LocalGenerators.neg_evolve h⟩⟩

open Classical in
/-- Time reversal. If the family is negation-contractive, then under the hypotheses of the
path-sum bound with $t$ any real number,
$\|[e^{tL} a, b]\| \le 2\|a\|\|b\| \bigl([X \cap Y \ne \emptyset] + \sum_{k \ge 1}
\frac{(2|t|)^k}{k!} P_k(Y, X)\bigr)$ (the series converges), and the bound also holds with the
walk sums $W_k(Y, X)$ in place of $P_k(Y, X)$ (that series converges by the walk bound at time
$|t|$). -/
theorem time_reversal {Λ : Type*} {A : Type*} [CStarAlgebra A] {ι : Type*} [Fintype ι]
    {𝒜 : LinearAQFT.Net (Set Λ) A} (G : LocalGenerators ι 𝒜)
    (hc : LinearAQFT.Net.IsCausal (latticeIndex Λ) 𝒜) (h : G.NegContractive) (X Y : Set Λ)
    {a b : A} (ha : a ∈ 𝒜 X) (hb : b ∈ 𝒜 Y) (t : ℝ) :
    Summable (fun k : ℕ => (2 * |t|) ^ (k + 1) / ((k + 1).factorial : ℝ) * G.pathSum X Y (k + 1)) ∧
    ‖comm (G.evolve t a) b‖ ≤ 2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
      ∑' k : ℕ, (2 * |t|) ^ (k + 1) / ((k + 1).factorial : ℝ) * G.pathSum X Y (k + 1)) ∧
    ‖comm (G.evolve t a) b‖ ≤ 2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
      ∑' k : ℕ, (2 * |t|) ^ (k + 1) / ((k + 1).factorial : ℝ) * G.walkSum X Y (k + 1)) := by
  have e : (fun k : ℕ => (2 * |t|) ^ (k + 1) / ((k + 1).factorial : ℝ) * G.pathSum X Y (k + 1)) =
      G.seriesTerm X Y |t| := funext fun k => by
    rw [LocalGenerators.seriesTerm, LocalGenerators.coef, G.pathSum_eq_pathSumRec]
  rw [e]
  exact ⟨G.summable_seriesTerm X Y (abs_nonneg t), G.liebRobinson_abs hc h X Y ha hb t,
    G.liebRobinson_walk_abs hc h X Y ha hb t⟩

/-- The graded bracket of $a, b \in A$ with freely chosen labels $|a|, |b| \in \{0, 1\}$
(no grading of $A$ is assumed; $0$ is even, $1$ odd): $[a, b]_\pm = ab - (-1)^{|a||b|} ba$.
It is the commutator
$ab - ba$ when either element is even and the anticommutator $ab + ba$ when both are odd, and
$\|[a, b]_\pm\| \le 2\|a\|\|b\|$. -/
theorem graded_bracket {A : Type*} [CStarAlgebra A] (oddA oddB : Bool) (a b : A) :
    gradedComm oddA oddB a b = a * b - (if oddA && oddB then -1 else 1 : ℂ) • (b * a) ∧
    gradedComm false oddB a b = a * b - b * a ∧ gradedComm oddA false a b = a * b - b * a ∧
    gradedComm true true a b = a * b + b * a ∧
    ‖gradedComm oddA oddB a b‖ ≤ 2 * ‖a‖ * ‖b‖ :=
  ⟨rfl, gradedComm_false_left oddB a b, gradedComm_false_right oddA a b,
    gradedComm_true_true a b, norm_gradedComm_le oddA oddB a b⟩

/-! ## Hamiltonian families

Conventions: for a self-adjoint Hamiltonian $H$, the generator is $L a = i[H, a]$ and the
dynamics is $a \mapsto e^{itH} a e^{-itH}$. -/

/-- Hamiltonian families. Given finite supports $S_i$ and elements $\Phi_i$ of $A$ for
$i \in \iota$, there is a Hamiltonian family on $\mathcal A$ with these data exactly when every
$\Phi_i$ lies in $\mathcal A(S_i)$ and is self-adjoint. The family is determined by its data. -/
theorem interaction_iff {Λ : Type*} {A : Type*} [CStarAlgebra A] {ι : Type*} [Fintype ι]
    (𝒜 : LinearAQFT.Net (Set Λ) A) (s : ι → Finset Λ) (Φ : ι → A) :
    ((∃ H : Interaction ι 𝒜, H.supp = s ∧ H.term = Φ) ↔
      (∀ i, Φ i ∈ 𝒜 (s i : Set Λ)) ∧ ∀ i, IsSelfAdjoint (Φ i)) ∧
    ∀ H H' : Interaction ι 𝒜, H.supp = H'.supp → H.term = H'.term → H = H' := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨H, rfl, rfl⟩
    exact ⟨H.term_mem, H.term_selfAdjoint⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨s, Φ, h1, h2⟩, rfl, rfl⟩
  · rintro ⟨s, Φ, _, _⟩ ⟨s', Φ', _, _⟩ hs hΦ
    cases hs; cases hΦ
    rfl

/-- The Hamiltonian family as local generators. For $x \in A$ the derivation is
$\mathrm{ad}_x(a) = i[x, a]$. For a Hamiltonian family $(S_i, \Phi_i)$ in a nonzero C*-algebra,
with $H_J = \sum_{i \in J} \Phi_i$ and $H = H_\iota$ the full Hamiltonian: the family of local
generators of $(S_i, \Phi_i)$ has supports $S_i$, generators $L_i = \mathrm{ad}_{\Phi_i}$ and
strengths $\kappa_i = \|\Phi_i\|$; it is negation-contractive; $U_t = e^{itH}$ is unitary; and
the dynamics is the conjugation $e^{tL} a = U_t a U_t^*$. -/
theorem hamiltonian_generators {Λ : Type*} {A : Type*} [CStarAlgebra A] [Nontrivial A]
    {ι : Type*} [Fintype ι] {𝒜 : LinearAQFT.Net (Set Λ) A} (H : Interaction ι 𝒜) :
    (∀ x a : A, derivation x a = Complex.I • (x * a - a * x)) ∧
    (∀ J : Finset ι, H.hamiltonian J = ∑ i ∈ J, H.term i) ∧
    H.toGenerators.supp = H.supp ∧ (∀ i, H.toGenerators.L i = derivation (H.term i)) ∧
    (∀ i, H.toGenerators.kappa i = ‖H.term i‖) ∧ H.toGenerators.NegContractive ∧
    (∀ t : ℝ, H.unitaryAt t =
      NormedSpace.exp (Complex.I • ((t : ℂ) • H.hamiltonian Finset.univ))) ∧
    (∀ t : ℝ, H.unitaryAt t ∈ unitary A) ∧
    ∀ (t : ℝ) (a : A), H.toGenerators.evolve t a = H.unitaryAt t * a * star (H.unitaryAt t) :=
  ⟨fun x a => derivation_apply x a, fun _ => rfl, rfl, fun _ => rfl, fun _ => rfl,
    H.toGenerators_negContractive, fun _ => rfl, H.unitaryAt_mem, H.evolve_eq_conj⟩

/-! ## Hamiltonian dynamics: the hypotheses and the role exchange

Let $\mathcal A$ be a net over the subsets of a set $\Lambda$ of sites in a C*-algebra $A$. The
derivation of $x \in A$ is $\mathrm{ad}_x a = i[x, a]$. A Hamiltonian family
$(S_i, \Phi_i)_{i \in I}$, indexed by a finite set $I$, has finite supports $S_i \subseteq
\Lambda$ and self-adjoint terms $\Phi_i \in \mathcal A(S_i)$; its Hamiltonian is
$H = \sum_i \Phi_i$, $U_t = \exp(itH)$, its local generators are $(S_i, \mathrm{ad}_{\Phi_i},
\|\Phi_i\|)$, and $A(t) = e^{tL} a$ with $L = \sum_i \mathrm{ad}_{\Phi_i}$. Norms of maps of $A$
are operator norms. For regions $X$, $Y$, $[X \cap Y \neq \emptyset]$ is $1$ if $X$ and $Y$ meet
and $0$ otherwise. -/

/-- Hamiltonian families satisfy the three hypotheses of the path-sum bound, the third by
unitarity. Let $A$ be nontrivial. For $x \in \mathcal A(S)$ and every $c \in A$,
$\|\mathrm{ad}_x c\| \le \|x\| N_S(c)$ (locality in the argument with strength $\|x\|$), and
$\mathrm{ad}_x c \in \mathcal A(Z \cup S)$ whenever $c \in \mathcal A(Z)$ (support closure). For
a Hamiltonian family $(S_i, \Phi_i)_{i \in I}$, every sub-family $J \subseteq I$ and every real
$t$, of either sign, $\|\exp(t \sum_{i \in J} \mathrm{ad}_{\Phi_i})\| \le 1$ (contraction); for
every real $t$, $U_t^* = U_{-t}$, and $\|A(t)\| = \|a\|$ for every $a \in A$. -/
theorem spin_hamiltonian_hypotheses {Λ : Type*} {A : Type*} [CStarAlgebra A] [Nontrivial A]
    (𝒜 : LinearAQFT.Net (Set Λ) A) {ι : Type*} [Fintype ι] (Φ : Interaction ι 𝒜) :
    (∀ (S Z : Set Λ) (x c : A), x ∈ 𝒜 S →
      ‖derivation x c‖ ≤ ‖x‖ * commNorm 𝒜 S c ∧ (c ∈ 𝒜 Z → derivation x c ∈ 𝒜 (Z ∪ S))) ∧
    (∀ (J : Finset ι) (t : ℝ), ‖NormedSpace.exp (t • ∑ i ∈ J, derivation (Φ.term i))‖ ≤ 1) ∧
    ∀ t : ℝ, star (Φ.unitaryAt t) = Φ.unitaryAt (-t) ∧
      ∀ a : A, ‖Φ.toGenerators.evolve t a‖ = ‖a‖ :=
  ⟨fun _ _ _ c hx => ⟨norm_derivation_apply_le 𝒜 hx c, fun hc => derivation_apply_mem 𝒜 hx hc⟩,
    fun J t => Φ.norm_exp_subfamily_le_one J t, fun t => ⟨Φ.star_unitaryAt t, fun a => by
      rw [Φ.evolve_eq_conj, norm_conj_eq (Φ.unitaryAt_mem t)]⟩⟩

open Classical in
/-- Role exchange ([Nachtergaele–Sims–Young 2019], eqs. (3.24) and (3.39)). Let $A$ be
nontrivial. For a unitary $U \in A$ and $a, b \in A$, $\|[U a U^*, b]\| = \|[a, U^* b U]\|$.
For a Hamiltonian family, every real $t$ and $a, b \in A$,
$\|[A(t), b]\| = \|[B(-t), a]\|$, where $B(s) = e^{sL} b$. If moreover the net is causal for
the lattice causal index, $a \in \mathcal A(X)$ and $b \in \mathcal A(Y)$, then for every real
$t$ the walk series of the pairs $(Y, X)$ and $(X, Y)$ at time $|t|$ converge and
$\|[A(t), b]\| \le 2\|a\|\|b\|\Bigl([X \cap Y \neq \emptyset] + \min\Bigl\{\sum_{k \ge 0}
\omega_k(Y, X; |t|), \sum_{k \ge 0} \omega_k(X, Y; |t|)\Bigr\}\Bigr)$,
where $\omega_k(Y, X; s) = \frac{(2s)^{k+1}}{(k+1)!} W_{k+1}(Y, X)$ are the walk terms of the
pair $(Y, X)$ for the strengths $\|\Phi_i\|$, with $\partial$ the boundaries and $T$ the
touched sites of the family; and for every decay kernel $(F, C_F)$ and every
$F$-bound $N$ of the family,
$\|[A(t), b]\| \le 2\|a\|\|b\|\Bigl([X \cap Y \neq \emptyset] +
\frac{e^{2 N C_F |t|} - 1}{C_F} \min\{\Sigma_F(Y, X), \Sigma_F(X, Y)\}\Bigr)$,
where $\Sigma_F(Y, X) = \sum_{y \in \partial Y} \sum_{x \in X \cap T} F(y, x)$. -/
theorem spin_role_exchange {Λ : Type*} {A : Type*} [CStarAlgebra A] [Nontrivial A]
    {𝒜 : LinearAQFT.Net (Set Λ) A} {ι : Type*} [Fintype ι] (Φ : Interaction ι 𝒜) :
    (∀ U : A, U ∈ unitary A → ∀ a b : A, ‖comm (U * a * star U) b‖ = ‖comm a (star U * b * U)‖) ∧
    (∀ (t : ℝ) (a b : A),
      ‖comm (Φ.toGenerators.evolve t a) b‖ = ‖comm (Φ.toGenerators.evolve (-t) b) a‖) ∧
    (LinearAQFT.Net.IsCausal (latticeIndex Λ) 𝒜 → ∀ (X Y : Set Λ) (a b : A), a ∈ 𝒜 X →
      b ∈ 𝒜 Y → ∀ t : ℝ,
      Summable (Φ.toGenerators.walkTerm X Y |t|) ∧ Summable (Φ.toGenerators.walkTerm Y X |t|) ∧
      ‖comm (Φ.toGenerators.evolve t a) b‖ ≤
        2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
          min (∑' k, Φ.toGenerators.walkTerm X Y |t| k)
            (∑' k, Φ.toGenerators.walkTerm Y X |t| k)) ∧
      ∀ (K : DecayKernel Λ) (N : ℝ), Φ.toGenerators.IsFBound K N →
        ‖comm (Φ.toGenerators.evolve t a) b‖ ≤
          2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
            (Real.exp (2 * N * K.CF * |t|) - 1) / K.CF *
              min (Φ.toGenerators.kernelSum K X Y) (Φ.toGenerators.kernelSum K Y X))) :=
  ⟨fun _ hU a b => Interaction.norm_comm_conj_eq hU a b, fun t a b => Φ.norm_comm_evolve_eq t a b,
    fun hc X Y _ _ ha hb t => ⟨Φ.toGenerators.summable_walkTerm X Y (abs_nonneg t),
      Φ.toGenerators.summable_walkTerm Y X (abs_nonneg t), Φ.liebRobinson_walk_min hc X Y ha hb t,
      fun K _ hN => Φ.liebRobinson_decay_min hc K hN X Y ha hb t⟩⟩

/-! ## Qudit lattices

Let $\Lambda$ be a finite set of sites, each site $u$ carrying a finite alphabet $\Omega_u$. A
configuration is a choice $s = (s(u))_{u \in \Lambda}$ of a letter at each site. For a region
$X \subseteq \Lambda$ a matrix on the letters of $X$ is a complex matrix indexed by the choices
of letters at the sites of $X$, and $s|_X$ is the restriction of $s$ to $X$. -/

open scoped Matrix.Norms.L2Operator in
open Classical in
/-- The qudit algebra and its local algebras. The qudit algebra is the algebra of complex
matrices indexed by the configurations, with the operator norm of the matrix acting on the
Euclidean space of complex functions on the configurations. The embedding of a matrix $m$ on
the letters of a region $X$ is the matrix $\iota_X m$ with $(\iota_X m)_{s s'} = m_{s|_X,
s'|_X}$ if $s$ and $s'$ agree at every site outside $X$, and $0$ otherwise. A matrix $M$ lies
in the local algebra $\mathcal A(X)$ of the qudit net exactly when (1) $M_{s s'} = 0$ whenever
$s$ and $s'$ differ at some site outside $X$, and (2) $M_{s s'} = M_{r r'}$ whenever $s$, $s'$
agree outside $X$, $r$, $r'$ agree outside $X$, $s = r$ on $X$ and $s' = r'$ on $X$.
$\mathcal A(\Lambda)$ is the whole qudit algebra, and the qudit net is causal for the lattice
causal index. If every alphabet is nonempty, $\mathcal A(X)$ consists exactly of the
embeddings $\iota_X m$. -/
theorem spin_qudit_net {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (σ : Λ → Type*)
    [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] :
    Qudit.Config σ = ((u : Λ) → σ u) ∧
    Qudit.QuditAlgebra σ = Matrix ((u : Λ) → σ u) ((u : Λ) → σ u) ℂ ∧
    (∀ M : Qudit.QuditAlgebra σ,
      ‖M‖ = ‖Matrix.toEuclideanCLM (n := (u : Λ) → σ u) (𝕜 := ℂ) M‖) ∧
    (∀ (X : Set Λ) (m : Matrix ((x : X) → σ x) ((x : X) → σ x) ℂ) (s s' : (u : Λ) → σ u),
      Qudit.embed X m s s' =
        if (∀ u, u ∉ X → s u = s' u) then m (fun x => s x) (fun x => s' x) else 0) ∧
    (∀ (X : Set Λ) (M : Qudit.QuditAlgebra σ), M ∈ Qudit.quditNet σ X ↔
      (∀ s s' : (u : Λ) → σ u, ¬ (∀ u, u ∉ X → s u = s' u) → M s s' = 0) ∧
      ∀ s s' r r' : (u : Λ) → σ u, (∀ u, u ∉ X → s u = s' u) → (∀ u, u ∉ X → r u = r' u) →
        (∀ u ∈ X, s u = r u) → (∀ u ∈ X, s' u = r' u) → M s s' = M r r') ∧
    (∀ M : Qudit.QuditAlgebra σ, M ∈ Qudit.quditNet σ Set.univ) ∧
    LinearAQFT.Net.IsCausal (latticeIndex Λ) (Qudit.quditNet σ) ∧
    ((∀ u, Nonempty (σ u)) → ∀ (X : Set Λ) (M : Qudit.QuditAlgebra σ),
      M ∈ Qudit.quditNet σ X ↔ ∃ m, M = Qudit.embed X m) := by
  refine ⟨rfl, rfl, fun M => rfl, fun X m s s' => ?_, fun X M => ?_, fun M => ?_,
    Qudit.quditNet_isCausal, fun h X M => ?_⟩
  · rw [Qudit.embed_apply]
    exact if_congr Iff.rfl rfl rfl
  · change Qudit.IsLocal X M ↔ _
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun s s' r r' hs hr e1 e2 =>
        h2 s s' r r' hs hr (funext fun x => e1 x x.2) (funext fun x => e2 x x.2)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun s s' r r' hs hr e1 e2 =>
        h2 s s' r r' hs hr (fun u hu => congrFun e1 ⟨u, hu⟩) (fun u hu => congrFun e2 ⟨u, hu⟩)⟩
  · change M ∈ Qudit.localAlgebra Set.univ
    rw [Qudit.localAlgebra_univ]
    exact StarSubalgebra.mem_top
  · have := h
    exact Qudit.mem_localAlgebra_iff

open Classical in
/-- Single-site operators. Let every site carry the same finite alphabet $\Omega$. For a site
$u$ and a matrix $m$ on $\Omega$, the single-site operator $m_u$ has the entries
$(m_u)_{s s'} = m_{s(u), s'(u)}$ if $s$ and $s'$ agree at every site other than $u$, and $0$
otherwise. It lies in $\mathcal A(\{u\})$; $m_u m'_u = (m m')_u$ and $(m_u)^* = (m^*)_u$; and
for sites $u \neq v$, $m_u$ and $m'_v$ commute, and
$(m_u m'_v)_{s s''} = m_{s(u), s''(u)} m'_{s(v), s''(v)}$ whenever $s$ and $s''$ agree at every
site other than $u$ and $v$. -/
theorem spin_siteOp {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {α : Type*} [Fintype α]
    [DecidableEq α] :
    (∀ (u : Λ) (m : Matrix α α ℂ) (s s' : Λ → α),
      Qudit.siteOp u m s s' = if (∀ v, v ≠ u → s v = s' v) then m (s u) (s' u) else 0) ∧
    (∀ (u : Λ) (m : Matrix α α ℂ), Qudit.siteOp u m ∈ Qudit.quditNet (fun _ : Λ => α) {u}) ∧
    (∀ (u : Λ) (m m' : Matrix α α ℂ),
      Qudit.siteOp u m * Qudit.siteOp u m' = Qudit.siteOp u (m * m')) ∧
    (∀ (u : Λ) (m : Matrix α α ℂ), star (Qudit.siteOp u m) = Qudit.siteOp u (star m)) ∧
    ∀ u v : Λ, u ≠ v → ∀ m m' : Matrix α α ℂ,
      Commute (Qudit.siteOp u m) (Qudit.siteOp v m') ∧
      ∀ s s'' : Λ → α, (∀ w, w ≠ u → w ≠ v → s w = s'' w) →
        (Qudit.siteOp u m * Qudit.siteOp v m') s s'' = m (s u) (s'' u) * m' (s v) (s'' v) := by
  refine ⟨fun u m s s' => ?_, fun u m => Qudit.isLocal_siteOp u m, Qudit.siteOp_mul_same,
    Qudit.star_siteOp, fun u v huv m m' => ⟨Qudit.siteOp_commute_of_ne huv m m', fun s s'' h => ?_⟩⟩
  · rw [Qudit.siteOp_apply]
    exact if_congr ⟨fun h v hv => h v (by simpa using hv), fun h v hv => h v (by simpa using hv)⟩
      rfl rfl
  · refine Qudit.siteOp_mul_apply_of_ne huv m m' s s'' fun w hw => h w ?_ ?_
    · intro e; exact hw (Or.inl e)
    · intro e; exact hw (Or.inr e)

open scoped Matrix.Norms.L2Operator in
/-- Qudit interactions. Let every alphabet be finite and nonempty. A qudit interaction indexed
by a finite set $I$ consists of finite supports $S_i \subseteq \Lambda$ and Hermitian matrices
$m_i$ on the letters of $S_i$; for all such supports and matrices there is a qudit interaction
with the supports $S_i$ whose Hamiltonian family has the terms $\Phi_i = \iota_{S_i} m_i$. For
every qudit interaction the matrices are Hermitian, its Hamiltonian family on the qudit net has
the same supports and the terms $\Phi_i = \iota_{S_i} m_i$, and its family of local generators
is that of its Hamiltonian family. -/
theorem spin_quditInteraction {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (σ : Λ → Type*)
    [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] [∀ u, Nonempty (σ u)] (ι : Type*)
    [Fintype ι] :
    (∀ (S : ι → Finset Λ)
      (m : ∀ i, Matrix ((x : (↑(S i) : Set Λ)) → σ x) ((x : (↑(S i) : Set Λ)) → σ x) ℂ),
      (∀ i, (m i).IsHermitian) → ∃ Φ : Qudit.QuditInteraction ι σ,
        Φ.supp = S ∧ ∀ i, Φ.toInteraction.term i = Qudit.embed (↑(S i)) (m i)) ∧
    ∀ Φ : Qudit.QuditInteraction ι σ, (∀ i, (Φ.mat i).IsHermitian) ∧
      Φ.toInteraction.supp = Φ.supp ∧
      (∀ i, Φ.toInteraction.term i = Qudit.embed (↑(Φ.supp i)) (Φ.mat i)) ∧
      Φ.toGenerators = Φ.toInteraction.toGenerators :=
  ⟨fun S m hm => ⟨⟨S, m, hm⟩, rfl, fun _ => rfl⟩,
    fun Φ => ⟨Φ.mat_isHermitian, rfl, fun _ => rfl, rfl⟩⟩

/-! ## The published bounds for spin systems

Let $\Lambda$ be a finite set of sites with finite nonempty alphabets, and
$(S_i, m_i)_{i \in I}$ a qudit interaction with the terms $\Phi_i = \iota_{S_i} m_i$, the
strengths $\kappa_i = \|\Phi_i\|$, the touched sites $T$, the boundaries $\partial Y$ and the site
matrix $h$; $A(t) = e^{tL} a$ is its dynamics. -/

open scoped Matrix.Norms.L2Operator in
open Classical in
/-- The spin-system Lieb–Robinson bound in matrix form (the bound of [Chen–Lucas–Yin 2023],
eq. (3.36), with the identity subtracted and the sum restricted to the boundary and the touched
sites). Here $e^{2|t|h}$ is the exponential of the site matrix, regarded as the real
$\Lambda \times \Lambda$ matrix with entries $h_{u v}$, and $1$ is the identity matrix. For
$a \in \mathcal A(X)$, $b \in \mathcal A(Y)$ and every real $t$,
$\|[A(t), b]\| \le 2\|a\|\|b\|\Bigl([X \cap Y \neq \emptyset] + \min\Bigl\{
\sum_{y \in \partial Y} \sum_{x \in X \cap T} (e^{2|t|h} - 1)_{y x},
\sum_{x \in \partial X} \sum_{y \in Y \cap T} (e^{2|t|h} - 1)_{x y}\Bigr\}\Bigr)$. -/
theorem spin_qudit_bound_matrix {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {σ : Λ → Type*}
    [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] [∀ u, Nonempty (σ u)] {ι : Type*}
    [Fintype ι] (Φ : Qudit.QuditInteraction ι σ) (X Y : Set Λ) {a b : Qudit.QuditAlgebra σ}
    (ha : a ∈ Qudit.quditNet σ X) (hb : b ∈ Qudit.quditNet σ Y) (t : ℝ) :
    ‖comm (Φ.toGenerators.evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
        min (∑ y ∈ Φ.toGenerators.boundary Y, ∑ x ∈ Φ.toGenerators.regionSites X,
            (NormedSpace.exp ((2 * |t|) • Matrix.of fun u v => Φ.toGenerators.siteMatrix u v) y x -
              (1 : Matrix Λ Λ ℝ) y x))
          (∑ x ∈ Φ.toGenerators.boundary X, ∑ y ∈ Φ.toGenerators.regionSites Y,
            (NormedSpace.exp ((2 * |t|) • Matrix.of fun u v => Φ.toGenerators.siteMatrix u v) x y -
              (1 : Matrix Λ Λ ℝ) x y))) := by
  rw [show (Matrix.of fun u v => Φ.toGenerators.siteMatrix u v) = Φ.toGenerators.toMatrix from
    rfl]
  have h1 := Φ.liebRobinson_matrixExp X Y ha hb t
  have h2 := Φ.toInteraction.liebRobinson_walk_exchange Qudit.quditNet_isCausal X Y ha hb t
  set_option backward.isDefEq.respectTransparency false in
  rw [Φ.toInteraction.toGenerators.tsum_walkTerm_eq Y X |t|] at h2
  rcases le_total
    (∑ y ∈ Φ.toGenerators.boundary Y, ∑ x ∈ Φ.toGenerators.regionSites X,
      (NormedSpace.exp ((2 * |t|) • Φ.toGenerators.toMatrix) y x - (1 : Matrix Λ Λ ℝ) y x))
    (∑ x ∈ Φ.toGenerators.boundary X, ∑ y ∈ Φ.toGenerators.regionSites Y,
      (NormedSpace.exp ((2 * |t|) • Φ.toGenerators.toMatrix) x y - (1 : Matrix Λ Λ ℝ) x y))
    with h | h
  · rw [min_eq_left h]; exact h1
  · rw [min_eq_right h]; exact h2

open scoped Matrix.Norms.L2Operator in
open Classical in
/-- The spin-system Lieb–Robinson bound in decay form (Theorem 3.1 of [Nachtergaele–Sims–Young
2019] for time-independent interactions). For a decay function $(F, C_F)$ and an $F$-bound $N$
of the interaction, $a \in \mathcal A(X)$, $b \in \mathcal A(Y)$ and every real $t$,
$\|[A(t), b]\| \le 2\|a\|\|b\|\Bigl([X \cap Y \neq \emptyset] +
\frac{e^{2 N C_F |t|} - 1}{C_F} \min\{\Sigma_F(Y, X), \Sigma_F(X, Y)\}\Bigr)$,
with $\Sigma_F(Y, X) = \sum_{y \in \partial Y} \sum_{x \in X \cap T} F(y, x)$. If $\Lambda$ is
nonempty and $F > 0$, the $F$-norm $\|\Phi\|_F = \max_{x, y} h_{x y} / F(x, y)$ (their
eq. (3.14)) is an $F$-bound and the least one. For a function $d$ on pairs of sites with
$d(x, y) \le d(x, z) + d(z, y)$ and $\mu \ge 0$, the weighted function
$F_\mu(x, y) = e^{-\mu d(x, y)} F(x, y)$ is a decay kernel with the same constant $C_F$ (their
eq. (3.11)). -/
theorem spin_qudit_bound_decay {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {σ : Λ → Type*}
    [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] [∀ u, Nonempty (σ u)] {ι : Type*}
    [Fintype ι] (Φ : Qudit.QuditInteraction ι σ) (K : DecayKernel Λ) :
    (∀ N : ℝ, Φ.toGenerators.IsFBound K N → ∀ (X Y : Set Λ) (a b : Qudit.QuditAlgebra σ),
      a ∈ Qudit.quditNet σ X → b ∈ Qudit.quditNet σ Y → ∀ t : ℝ,
      ‖comm (Φ.toGenerators.evolve t a) b‖ ≤
        2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
          (Real.exp (2 * N * K.CF * |t|) - 1) / K.CF *
            min (Φ.toGenerators.kernelSum K X Y) (Φ.toGenerators.kernelSum K Y X))) ∧
    (∀ [Nonempty Λ], (∀ x y, 0 < K.F x y) →
      Φ.toGenerators.fNorm K.F = Finset.univ.sup' Finset.univ_nonempty
        (fun p : Λ × Λ => Φ.toGenerators.siteMatrix p.1 p.2 / K.F p.1 p.2) ∧
      Φ.toGenerators.IsFBound K (Φ.toGenerators.fNorm K.F) ∧
      ∀ N : ℝ, Φ.toGenerators.IsFBound K N → Φ.toGenerators.fNorm K.F ≤ N) ∧
    ∀ (d : Λ → Λ → ℝ) (hd : ∀ x y z, d x y ≤ d x z + d z y) (μ : ℝ) (hμ : 0 ≤ μ),
      (∀ x y, (K.expWeight d hd hμ).F x y = Real.exp (-μ * d x y) * K.F x y) ∧
      (K.expWeight d hd hμ).CF = K.CF := by
  refine ⟨fun N hN X Y a b ha hb t => Φ.liebRobinson_decay K hN X Y ha hb t, ?_,
    fun d hd μ hμ => ⟨fun _ _ => rfl, rfl⟩⟩
  intro _ hF
  exact ⟨rfl, Φ.toGenerators.isFBound_fNorm K hF,
    fun N hN => Φ.toGenerators.fNorm_le_of_isFBound K hF hN⟩

open scoped Matrix.Norms.L2Operator in
open Classical in
/-- The spin-system Lieb–Robinson bound under bounded geometry, with the light cone. Let the
interaction have bounded geometry with the distance $d$, the diameter bound $\rho$ and the
velocity $v$, let $r \ge 1$ be an integer with $(r - 1)\rho < d(y, x)$ for all
$y \in \partial Y$ and $x \in X \cap T$, $a \in \mathcal A(X)$, $b \in \mathcal A(Y)$ and
$t \ge 0$. Then
$\|[A(t), b]\| \le 2\|a\|\|b\|([X \cap Y \neq \emptyset] + |\partial Y| \frac{(vt)^r}{r!}
e^{vt})$, and for every real $\mu$,
$\|[A(t), b]\| \le 2\|a\|\|b\|([X \cap Y \neq \emptyset] + |\partial Y| e^{vt} e^{-\mu r}
(e^{e^\mu v t} - 1))$. -/
theorem spin_qudit_bound_geometry {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {σ : Λ → Type*}
    [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] [∀ u, Nonempty (σ u)] {ι : Type*}
    [Fintype ι] (Φ : Qudit.QuditInteraction ι σ) (B : Φ.toGenerators.BoundedGeometry)
    (X Y : Set Λ) {r : ℕ} (hr : 1 ≤ r)
    (hd : ∀ y ∈ Φ.toGenerators.boundary Y, ∀ x ∈ Φ.toGenerators.regionSites X,
      ((r : ℝ) - 1) * B.rho < B.d y x)
    {a b : Qudit.QuditAlgebra σ} (ha : a ∈ Qudit.quditNet σ X) (hb : b ∈ Qudit.quditNet σ Y)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖comm (Φ.toGenerators.evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
        (Φ.toGenerators.boundary Y).card *
          ((B.v * t) ^ r / (r.factorial : ℝ) * Real.exp (B.v * t))) ∧
    ∀ μ : ℝ, ‖comm (Φ.toGenerators.evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
        (Φ.toGenerators.boundary Y).card * (Real.exp (B.v * t) *
          (Real.exp (-μ * r) * (Real.exp (Real.exp μ * (B.v * t)) - 1)))) :=
  ⟨Φ.liebRobinson_boundedGeometry B X Y hr hd ha hb ht,
    fun μ => Φ.liebRobinson_cone B X Y hr hd μ ha hb ht⟩

/-! ## The conditional expectation and the twirl

Let $\Lambda$ be a finite set of sites with finite nonempty alphabets. For a region $X$,
$\Omega_{X^c}$ is the set of choices $\eta$ of letters at the sites outside $X$, and
$(s|_X, \eta)$ is the configuration equal to $s$ on $X$ and to $\eta$ outside $X$. For the
twirl each alphabet is cyclic, $\Omega_u = \mathbb Z_{q_u}$ with $q_u \ge 1$, letters are added
modulo $q_u$, and
$e_n(k) = e^{2\pi i k / n}$, computed as $(e^{2\pi i / n})^{\bar k}$ with $\bar k \in \{0, \dots,
n - 1\}$ the representative of $k \in \mathbb Z_n$. -/

open Classical in
/-- The conditional expectation onto a region $X$ is the map $P_X$ of the qudit algebra with
$(P_X M)_{s s'} = \frac{1}{|\Omega_{X^c}|} \sum_{\eta \in \Omega_{X^c}}
M_{(s|_X, \eta), (s'|_X, \eta)}$
if $s$ and $s'$ agree at every site outside $X$, and $(P_X M)_{s s'} = 0$ otherwise. It maps
into $\mathcal A(X)$, is additive and complex homogeneous, commutes with the adjoint, satisfies
$P_X M = M$ for $M \in \mathcal A(X)$ and $P_X 1 = 1$; $P_\Lambda M = M$, and
$P_\emptyset M = (\operatorname{tr} M / |\Omega_\Lambda|) 1$, with $|\Omega_\Lambda|$ the number
of configurations. -/
theorem spin_condExp {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (σ : Λ → Type*)
    [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)] [∀ u, Nonempty (σ u)] :
    (∀ (X : Set Λ) (M : Qudit.QuditAlgebra σ) (s s' : (u : Λ) → σ u),
      Qudit.condExp X M s s' = if (∀ u, u ∉ X → s u = s' u) then
        (Fintype.card ((y : (Xᶜ : Set Λ)) → σ y) : ℂ)⁻¹ *
          ∑ η : (y : (Xᶜ : Set Λ)) → σ y,
            M (fun u => if h : u ∈ Xᶜ then η ⟨u, h⟩ else s u)
              (fun u => if h : u ∈ Xᶜ then η ⟨u, h⟩ else s' u) else 0) ∧
    (∀ (X : Set Λ) (M : Qudit.QuditAlgebra σ), Qudit.condExp X M ∈ Qudit.quditNet σ X) ∧
    (∀ (X : Set Λ) (M N : Qudit.QuditAlgebra σ),
      Qudit.condExp X (M + N) = Qudit.condExp X M + Qudit.condExp X N) ∧
    (∀ (X : Set Λ) (c : ℂ) (M : Qudit.QuditAlgebra σ),
      Qudit.condExp X (c • M) = c • Qudit.condExp X M) ∧
    (∀ (X : Set Λ) (M : Qudit.QuditAlgebra σ),
      star (Qudit.condExp X M) = Qudit.condExp X (star M)) ∧
    (∀ (X : Set Λ) (M : Qudit.QuditAlgebra σ), M ∈ Qudit.quditNet σ X →
      Qudit.condExp X M = M) ∧
    (∀ X : Set Λ, Qudit.condExp X (1 : Qudit.QuditAlgebra σ) = 1) ∧
    (∀ M : Qudit.QuditAlgebra σ, Qudit.condExp Set.univ M = M) ∧
    ∀ M : Qudit.QuditAlgebra σ, Qudit.condExp ∅ M =
      ((Fintype.card ((u : Λ) → σ u) : ℂ)⁻¹ * Matrix.trace M) • (1 : Qudit.QuditAlgebra σ) := by
  refine ⟨fun X M s s' => ?_, fun X M => Qudit.condExp_mem X M, Qudit.condExp_add,
    Qudit.condExp_smul, Qudit.star_condExp, fun X M hM => Qudit.condExp_of_isLocal hM,
    fun X => Qudit.condExp_one X, Qudit.condExp_univ, Qudit.condExp_empty⟩
  · rw [Qudit.condExp_apply]
    refine if_congr Iff.rfl ?_ rfl
    congr 1
    refine Finset.sum_congr rfl fun η _ => ?_
    unfold Qudit.glue
    congr 1 <;> funext u <;> split_ifs <;> rfl

open scoped Matrix.Norms.L2Operator in
open Classical in
/-- Weyl unitaries and the twirl, for cyclic alphabets. For a region $Y$ and choices $\xi$,
$\eta$ of letters at the sites of $Y$, the Weyl unitary $V_{\xi, \eta}$ has the entries
$(V_{\xi, \eta})_{s s'} = \psi_\eta(s')$ if $s = s' + \xi$ (that is, $s(u) = s'(u) + \xi(u)$
for $u \in Y$ and $s(u) = s'(u)$ for $u \notin Y$), and $0$ otherwise, where
$\psi_\eta(s) = \prod_{u \in Y} e_{q_u}(\eta(u) s(u))$. It is unitary and lies in
$\mathcal A(Y)$. For every region $X$ and every matrix $M$ the twirl onto $X$,
$|\Omega_{X^c}|^{-2} \sum_{\xi, \eta \in \Omega_{X^c}} V_{\xi, \eta} M V_{\xi, \eta}^*$ over the
Weyl unitaries of the complement $X^c$, equals $P_X M$; hence $\|P_X M\| \le \|M\|$, and
$P_X(a M) = a P_X M$ and $P_X(M b) = (P_X M) b$ for $a, b \in \mathcal A(X)$. -/
theorem spin_twirl {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (q : Λ → ℕ) [∀ u, NeZero (q u)] :
    (∀ (Y : Set Λ) (ξ η : (y : Y) → ZMod (q y)) (s s' : (u : Λ) → ZMod (q u)),
      Qudit.weyl Y ξ η s s' =
        if s = (fun u => if h : u ∈ Y then s' u + ξ ⟨u, h⟩ else s' u) then
          ∏ y : Y, Complex.exp (2 * Real.pi * Complex.I / (q y : ℂ)) ^ (η y * s' y).val
        else 0) ∧
    (∀ (Y : Set Λ) (ξ η : (y : Y) → ZMod (q y)),
      Qudit.weyl Y ξ η ∈ unitary (Qudit.QuditAlgebra fun u => ZMod (q u)) ∧
      Qudit.weyl Y ξ η ∈ Qudit.quditNet (fun u => ZMod (q u)) Y) ∧
    (∀ (X : Set Λ) (M : Qudit.QuditAlgebra fun u => ZMod (q u)),
      ((Fintype.card ((y : (Xᶜ : Set Λ)) → ZMod (q y)) : ℂ) ^ 2)⁻¹ •
        ∑ ξ : (y : (Xᶜ : Set Λ)) → ZMod (q y), ∑ η : (y : (Xᶜ : Set Λ)) → ZMod (q y),
          Qudit.weyl Xᶜ ξ η * M * star (Qudit.weyl Xᶜ ξ η) = Qudit.condExp X M) ∧
    (∀ (X : Set Λ) (M : Qudit.QuditAlgebra fun u => ZMod (q u)),
      ‖Qudit.condExp X M‖ ≤ ‖M‖) ∧
    ∀ (X : Set Λ) (a b M : Qudit.QuditAlgebra fun u => ZMod (q u)),
      a ∈ Qudit.quditNet (fun u => ZMod (q u)) X → b ∈ Qudit.quditNet (fun u => ZMod (q u)) X →
      Qudit.condExp X (a * M) = a * Qudit.condExp X M ∧
        Qudit.condExp X (M * b) = Qudit.condExp X M * b := by
  refine ⟨fun Y ξ η s s' => ?_, fun Y ξ η => ⟨Qudit.weyl_mem_unitary Y ξ η, Qudit.weyl_mem Y ξ η⟩,
    fun X M => Qudit.twirl_eq_condExp X M, Qudit.norm_condExp_le,
    fun X a b M ha hb => ⟨Qudit.condExp_mul_left ha M, Qudit.condExp_mul_right hb M⟩⟩
  rw [Qudit.weyl_apply]
  by_cases h : s = Qudit.shiftBy Y ξ s'
  · have h' : s = (fun u => if h : u ∈ Y then s' u + ξ ⟨u, h⟩ else s' u) := h
    rw [ite_eq_left h, ite_eq_left h']
    rfl
  · have h' : ¬ s = (fun u => if h : u ∈ Y then s' u + ξ ⟨u, h⟩ else s' u) := h
    rw [ite_eq_right h, ite_eq_right h']

/-! ## Local approximation

Let $\mathcal A$ be a net over the subsets of a set $\Lambda$ of sites in a C*-algebra $A$, and
$N_S$ its commutator seminorms. -/

/-- Nets with local approximation and approximate locality. The net has local approximation
with the maps $P_X : A \to A$ exactly when $P_X c \in \mathcal A(X)$ and
$\|c - P_X c\| \le N_{X^c}(c)$ for every region $X$ and every $c \in A$. If the net is causal
for the lattice causal index, $N_Y(c) \le 2\|c - c'\|$ for every $c \in A$ whenever
$c' \in \mathcal A(X)$ and $Y$ is disjoint from $X$. A map
$\mathcal T : A \to A$ is $\varepsilon$-local with the neighbourhood map $\mathcal N$ (a map
from regions to regions) exactly when for every region $O$ and every $c \in \mathcal A(O)$
there is $c' \in \mathcal A(\mathcal N(O))$ with $\|\mathcal T c - c'\| \le \varepsilon \|c\|$;
it is $0$-local exactly when $\mathcal T(\mathcal A(O)) \subseteq \mathcal A(\mathcal N(O))$
for every region $O$. -/
theorem spin_localApprox_iff {Λ : Type*} {A : Type*} [CStarAlgebra A]
    (𝒜 : LinearAQFT.Net (Set Λ) A) (P : Set Λ → A → A) :
    ((∃ Q : LocalApprox 𝒜, Q.P = P) ↔
      (∀ (X : Set Λ) (c : A), P X c ∈ 𝒜 X) ∧ ∀ (X : Set Λ) (c : A),
        ‖c - P X c‖ ≤ commNorm 𝒜 Xᶜ c) ∧
    (LinearAQFT.Net.IsCausal (latticeIndex Λ) 𝒜 → ∀ X Y : Set Λ, Disjoint X Y →
      ∀ c c' : A, c' ∈ 𝒜 X → commNorm 𝒜 Y c ≤ 2 * ‖c - c'‖) ∧
    ∀ (T : A → A) (nbhd : Set Λ → Set Λ) (ε : ℝ),
      (IsApproxLocalWith 𝒜 T nbhd ε ↔
        ∀ O : Set Λ, ∀ x ∈ 𝒜 O, ∃ y ∈ 𝒜 (nbhd O), ‖T x - y‖ ≤ ε * ‖x‖) ∧
      (IsApproxLocalWith 𝒜 T nbhd 0 ↔ ∀ O : Set Λ, ∀ x ∈ 𝒜 O, T x ∈ 𝒜 (nbhd O)) := by
  refine ⟨⟨?_, fun ⟨h1, h2⟩ => ⟨⟨P, h1, h2⟩, rfl⟩⟩,
    fun hc X Y hXY c c' hc' => commNorm_le_two_mul_norm_sub hc hXY hc',
    fun T nbhd ε => ⟨Iff.rfl, isApproxLocalWith_zero_iff⟩⟩
  rintro ⟨Q, rfl⟩
  exact ⟨Q.P_mem, Q.norm_sub_P_le⟩

open scoped Matrix.Norms.L2Operator in
/-- Local approximation on the qudit lattice. For a finite set $\Lambda$ of sites with cyclic
alphabets, every region $X$ and every
matrix $M$,
$\|M - P_X M\| \le N_{X^c}(M) \le 2 \|M - P_X M\|$,
where $N_{X^c}$ is the commutator seminorm of the qudit net for the complement $X^c$ and $P_X$
the conditional expectation onto $X$. The conditional expectations give the qudit net with
cyclic alphabets local approximation. -/
theorem spin_qudit_localApprox {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (q : Λ → ℕ)
    [∀ u, NeZero (q u)] :
    (∀ (X : Set Λ) (M : Qudit.QuditAlgebra fun u => ZMod (q u)),
      ‖M - Qudit.condExp X M‖ ≤ commNorm (Qudit.quditNet fun u => ZMod (q u)) Xᶜ M ∧
      commNorm (Qudit.quditNet fun u => ZMod (q u)) Xᶜ M ≤ 2 * ‖M - Qudit.condExp X M‖) ∧
    (Qudit.localApprox (q := q)).P = Qudit.condExp :=
  ⟨fun X M => ⟨Qudit.norm_sub_condExp_le_commNorm X M,
    Qudit.commNorm_compl_le_two_mul_norm_sub_condExp X M⟩, rfl⟩

/-! ## Truncated dynamics and the approximate automaton

Let $(S_i, L_i, \kappa_i)_{i \in I}$ be a family of local generators on a net over the subsets
of a set $\Lambda$ of sites in a C*-algebra $A$, causal for the lattice causal index, with local
approximation $P$; $T = \bigcup_i S_i$ is the set of touched sites, $A(t) = e^{tL} a$, and
$\omega_k(Y, X; t) = \frac{(2t)^{k+1}}{(k+1)!} W_{k+1}(Y, X)$ are the walk terms of a pair of
regions $(Y, X)$, with $\partial$ the boundaries of the family; termwise
$\omega_{k-1}(Y, X; t) = \frac{(2t)^k}{k!} W_k(Y, X)$, so that
$\sum_{k \ge 0} \omega_k(Y, X; t) = \sum_{k \ge 1} \frac{(2t)^k}{k!} W_k(Y, X)$ is the walk
series of the walk bound. A map $\mathcal T : A \to A$ is
$\varepsilon$-local with a neighbourhood map $\mathcal N$ (a map from regions to regions) if for
every region $O$ and every $c \in \mathcal A(O)$ there is $c' \in \mathcal A(\mathcal N(O))$ with
$\|\mathcal T c - c'\| \le \varepsilon \|c\|$. Under bounded geometry with the distance $d$ and
the diameter bound $\rho$, the $r$-neighbourhood of a region $O$, for an integer $r$, is
$O^{+r} = \{w : d(w, x) < r\rho \text{ for some } x \in O\}$. -/

/-- Truncated dynamics. For $a \in \mathcal A(X)$, a region $X' \supseteq X$, $Y = X'^c$ and
$t \ge 0$, the walk series of the pair $(Y, X)$ converges, and
$\|A(t) - P_{X'} A(t)\| \le 2\|a\| \sum_{k \ge 0} \omega_k(Y, X; t)$ and
$N_Y(A(t)) \le 2\|a\| \sum_{k \ge 0} \omega_k(Y, X; t)$.
Under bounded geometry with the distance $d$, the diameter bound $\rho$ and the velocity $v$,
if $r \ge 1$ is an integer with $(r - 1)\rho < d(y, x)$ for all $y \in \partial Y$ and
$x \in X \cap T$, then $\|A(t) - P_{X'} A(t)\| \le 2\|a\| |\partial Y| \frac{(vt)^r}{r!} e^{vt}$
and, for every real $\mu$,
$\|A(t) - P_{X'} A(t)\| \le 2\|a\| |\partial Y| e^{vt} e^{-\mu r} (e^{e^\mu v t} - 1)$. -/
theorem spin_truncated_dynamics {Λ : Type*} {A : Type*} [CStarAlgebra A]
    {𝒜 : LinearAQFT.Net (Set Λ) A} (hc : LinearAQFT.Net.IsCausal (latticeIndex Λ) 𝒜)
    (Q : LocalApprox 𝒜) {ι : Type*} [Fintype ι] (G : LocalGenerators ι 𝒜) {X X' : Set Λ}
    (hXX' : X ⊆ X') {a : A} (ha : a ∈ 𝒜 X) {t : ℝ} (ht : 0 ≤ t) :
    Summable (G.walkTerm X X'ᶜ t) ∧
    ‖G.evolve t a - Q.P X' (G.evolve t a)‖ ≤ 2 * ‖a‖ * ∑' k, G.walkTerm X X'ᶜ t k ∧
    commNorm 𝒜 X'ᶜ (G.evolve t a) ≤ 2 * ‖a‖ * ∑' k, G.walkTerm X X'ᶜ t k ∧
    ∀ (B : G.BoundedGeometry) (r : ℕ), 1 ≤ r →
      (∀ y ∈ G.boundary X'ᶜ, ∀ x ∈ G.regionSites X, ((r : ℝ) - 1) * B.rho < B.d y x) →
      ‖G.evolve t a - Q.P X' (G.evolve t a)‖ ≤
        2 * ‖a‖ * ((G.boundary X'ᶜ).card *
          ((B.v * t) ^ r / (r.factorial : ℝ) * Real.exp (B.v * t))) ∧
      ∀ μ : ℝ, ‖G.evolve t a - Q.P X' (G.evolve t a)‖ ≤
        2 * ‖a‖ * ((G.boundary X'ᶜ).card * (Real.exp (B.v * t) *
          (Real.exp (-μ * r) * (Real.exp (Real.exp μ * (B.v * t)) - 1)))) :=
  ⟨G.summable_walkTerm X X'ᶜ ht, G.norm_sub_P_evolve_le hc Q hXX' ha ht,
    G.commNorm_evolve_le hc X X'ᶜ (disjoint_compl_right.mono_left hXX') ha ht,
    fun B _ hr hd => ⟨G.norm_sub_P_evolve_le_geom hc Q B hXX' hr hd ha ht,
      fun μ => G.norm_sub_P_evolve_le_cone hc Q B hXX' hr hd μ ha ht⟩⟩

/-- The approximate automaton. Let $t \ge 0$; the $r$-neighbourhoods are as defined above.
(a) Let $\Lambda$ be finite and $\mathcal N$ a neighbourhood map. For every region $O$ the
series $\sum_{k \ge 0} \omega_k(\mathcal N(O)^c, O; t)$ converges; let $\varepsilon(t)$ be the
largest, over the finitely many regions $O$, of
$2 \sum_{k \ge 0} \omega_k(\mathcal N(O)^c, O; t)$. If $O \subseteq \mathcal N(O)$ for every
region $O$, then $e^{tL}$ is $\varepsilon(t)$-local with
$\mathcal N$. (b) Under bounded geometry with the diameter bound $\rho > 0$ and the velocity
$v$, and for an integer $r \ge 1$, $e^{tL}$ is $2|T| \frac{(vt)^r}{r!} e^{vt}$-local with
$O \mapsto O^{+r}$, and for every real $\mu$ it is
$2|T| e^{vt} e^{-\mu r} (e^{e^\mu v t} - 1)$-local with $O \mapsto O^{+r}$. -/
theorem spin_approx_automaton {Λ : Type*} {A : Type*} [CStarAlgebra A]
    {𝒜 : LinearAQFT.Net (Set Λ) A} (hc : LinearAQFT.Net.IsCausal (latticeIndex Λ) 𝒜)
    (Q : LocalApprox 𝒜) {ι : Type*} [Fintype ι] (G : LocalGenerators ι 𝒜) {t : ℝ}
    (ht : 0 ≤ t) :
    (∀ (B : G.BoundedGeometry) (r : ℕ) (O : Set Λ),
      G.neighbourhood B r O = {w | ∃ x ∈ O, B.d w x < r * B.rho}) ∧
    (Finite Λ → ∀ nbhd : Set Λ → Set Λ,
      (∀ O : Set Λ, Summable (G.walkTerm O (nbhd O)ᶜ t)) ∧
      G.truncError nbhd t = ⨆ O : Set Λ, 2 * ∑' k, G.walkTerm O (nbhd O)ᶜ t k ∧
      ((∀ O, O ⊆ nbhd O) → IsApproxLocalWith 𝒜 (G.evolve t) nbhd (G.truncError nbhd t))) ∧
    ∀ (B : G.BoundedGeometry), 0 < B.rho → ∀ r : ℕ, 1 ≤ r →
      IsApproxLocalWith 𝒜 (G.evolve t) (G.neighbourhood B r)
        (2 * G.touched.card * ((B.v * t) ^ r / (r.factorial : ℝ) * Real.exp (B.v * t))) ∧
      ∀ μ : ℝ, IsApproxLocalWith 𝒜 (G.evolve t) (G.neighbourhood B r)
        (2 * G.touched.card * (Real.exp (B.v * t) *
          (Real.exp (-μ * r) * (Real.exp (Real.exp μ * (B.v * t)) - 1)))) := by
  refine ⟨fun B r O => rfl, fun hΛ nbhd => ?_,
    fun B hρ r hr => ⟨G.evolve_isApproxLocalWith_geom hc Q B hρ hr ht,
      fun μ => G.evolve_isApproxLocalWith_cone hc Q B hρ hr μ ht⟩⟩
  exact ⟨fun O => G.summable_walkTerm O (nbhd O)ᶜ ht, rfl,
    fun hn => G.evolve_isApproxLocalWith hc Q nbhd hn ht⟩

open scoped Matrix.Norms.L2Operator in
/-- Truncated dynamics and the approximate automaton for spin systems. Let $\Lambda$ be a
finite set of sites with cyclic alphabets, $(S_i, m_i)_{i \in I}$ a qudit interaction with the
strengths $\kappa_i = \|\Phi_i\|$ and the touched sites $T$, $P$ the conditional expectations
and $t \ge 0$. For $a \in \mathcal A(X)$ and a region $X' \supseteq X$ the walk series of the
pair $(X'^c, X)$ converges and $\|A(t) - P_{X'} A(t)\| \le 2\|a\| \sum_{k \ge 0}
\omega_k(X'^c, X; t)$. Under bounded geometry with the distance $d$, the diameter bound
$\rho > 0$ and the velocity $v$, and for an integer $r \ge 1$, the dynamics $e^{tL}$ is
$2|T| \frac{(vt)^r}{r!} e^{vt}$-local and, for every real $\mu$,
$2|T| e^{vt} e^{-\mu r} (e^{e^\mu v t} - 1)$-local with the $r$-neighbourhood map
$O \mapsto O^{+r}$. -/
theorem spin_qudit_automaton {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {q : Λ → ℕ}
    [∀ u, NeZero (q u)] {ι : Type*} [Fintype ι]
    (Φ : Qudit.QuditInteraction ι fun u => ZMod (q u)) {t : ℝ} (ht : 0 ≤ t) :
    (∀ X X' : Set Λ, X ⊆ X' → ∀ a ∈ Qudit.quditNet (fun u => ZMod (q u)) X,
      Summable (Φ.toGenerators.walkTerm X X'ᶜ t) ∧
      ‖Φ.toGenerators.evolve t a - Qudit.condExp X' (Φ.toGenerators.evolve t a)‖ ≤
        2 * ‖a‖ * ∑' k, Φ.toGenerators.walkTerm X X'ᶜ t k) ∧
    ∀ (B : Φ.toGenerators.BoundedGeometry), 0 < B.rho → ∀ r : ℕ, 1 ≤ r →
      IsApproxLocalWith (Qudit.quditNet fun u => ZMod (q u)) (Φ.toGenerators.evolve t)
        (Φ.toGenerators.neighbourhood B r)
        (2 * Φ.toGenerators.touched.card *
          ((B.v * t) ^ r / (r.factorial : ℝ) * Real.exp (B.v * t))) ∧
      ∀ μ : ℝ, IsApproxLocalWith (Qudit.quditNet fun u => ZMod (q u)) (Φ.toGenerators.evolve t)
        (Φ.toGenerators.neighbourhood B r)
        (2 * Φ.toGenerators.touched.card * (Real.exp (B.v * t) *
          (Real.exp (-μ * r) * (Real.exp (Real.exp μ * (B.v * t)) - 1)))) :=
  ⟨fun X X' hXX' _ ha => ⟨Φ.toGenerators.summable_walkTerm X X'ᶜ ht,
      Φ.norm_sub_condExp_evolve_le hXX' ha ht⟩,
    fun B hρ _ hr => ⟨Φ.evolve_isApproxLocalWith_geom B hρ hr ht,
      fun μ => Φ.evolve_isApproxLocalWith_cone B hρ hr μ ht⟩⟩

/-! ## Open systems

Let $\mathcal A$ be a net over the subsets of a set $\Lambda$ of sites in a C*-algebra $A$. For
$\Gamma \in A$ the dissipator is
$\Delta_\Gamma a = \Gamma^* a \Gamma - \frac12 (\Gamma^* \Gamma a + a \Gamma^* \Gamma)$. A
Lindblad term on a finite region $S$ consists of a self-adjoint $H \in \mathcal A(S)$ (its
Hamiltonian part) and finitely many jump operators $\Gamma_1, \dots, \Gamma_m \in \mathcal A(S)$;
its generator is $L_S a = i[H, a] + \sum_j \Delta_{\Gamma_j} a$. Norms of maps of $A$ are
operator norms. -/

/-- Lindblad terms. For a finite region $S$, a self-adjoint $H \in \mathcal A(S)$ and
$\Gamma_1, \dots, \Gamma_m \in \mathcal A(S)$ there is a Lindblad term with support $S$,
Hamiltonian part $H$ and the generator $L_S a = i[H, a] + \sum_j \Delta_{\Gamma_j} a$ (only the
generator is fixed: the term's jump operators are not asserted to be
$\Gamma_1, \dots, \Gamma_m$, and the statements below hold for its own jump operators). For every
Lindblad term with support $S$, Hamiltonian part $H$ and jump operators $\Gamma_j$: $H$ is
self-adjoint, $H$ and the $\Gamma_j$ lie in $\mathcal A(S)$, and the generator has this form; it
satisfies $\|L_S\| \le 2\|H\| + 2\sum_j \|\Gamma_j\|^2$, maps $\mathcal A(Z)$ into
$\mathcal A(Z \cup S)$, satisfies $(L_S a)^* = L_S(a^*)$ and
$\|L_S c\| \le (\|H\| + \sum_j \|\Gamma_j\|^2) N_S(c)$ for every $c$. If the net is causal for
the lattice causal index, $L_S c = 0$ for $c \in \mathcal A(S^c)$, and for every local
approximation $P$ of the net and every $c$, $L_S c = L_S(c - P_{S^c} c)$ and
$\|L_S c\| \le \|L_S\| N_S(c)$. -/
theorem spin_lindbladTerm {Λ : Type*} {A : Type*} [CStarAlgebra A]
    (𝒜 : LinearAQFT.Net (Set Λ) A) :
    (∀ (S : Finset Λ) (H : A) (m : ℕ) (K : Fin m → A), H ∈ 𝒜 ↑S → IsSelfAdjoint H →
      (∀ j, K j ∈ 𝒜 ↑S) → ∃ T : LindbladTerm 𝒜, T.supp = S ∧ T.H = H ∧ ∀ a : A,
        T.gen a = Complex.I • comm H a + ∑ j, (star (K j) * a * K j -
          (2 : ℂ)⁻¹ • (star (K j) * K j * a) - (2 : ℂ)⁻¹ • (a * (star (K j) * K j)))) ∧
    ∀ T : LindbladTerm 𝒜,
      (T.H ∈ 𝒜 ↑T.supp ∧ IsSelfAdjoint T.H ∧ ∀ j, T.K j ∈ 𝒜 ↑T.supp) ∧
      (∀ a : A, T.gen a = Complex.I • comm T.H a + ∑ j, (star (T.K j) * a * T.K j -
        (2 : ℂ)⁻¹ • (star (T.K j) * T.K j * a) - (2 : ℂ)⁻¹ • (a * (star (T.K j) * T.K j)))) ∧
      ‖T.gen‖ ≤ 2 * ‖T.H‖ + 2 * ∑ j, ‖T.K j‖ ^ 2 ∧
      (∀ (Z : Set Λ) (c : A), c ∈ 𝒜 Z → T.gen c ∈ 𝒜 (Z ∪ ↑T.supp)) ∧
      (∀ a : A, star (T.gen a) = T.gen (star a)) ∧
      (∀ c : A, ‖T.gen c‖ ≤ (‖T.H‖ + ∑ j, ‖T.K j‖ ^ 2) * commNorm 𝒜 ↑T.supp c) ∧
      (LinearAQFT.Net.IsCausal (latticeIndex Λ) 𝒜 →
        (∀ c ∈ 𝒜 (↑T.supp : Set Λ)ᶜ, T.gen c = 0) ∧
        ∀ (Q : LocalApprox 𝒜) (c : A), T.gen c = T.gen (c - Q.P (↑T.supp : Set Λ)ᶜ c) ∧
          ‖T.gen c‖ ≤ ‖T.gen‖ * commNorm 𝒜 ↑T.supp c) := by
  refine ⟨fun S H m K hH hHs hK => ⟨⟨S, H, hH, hHs, m, K, hK⟩, rfl, rfl, fun a => ?_⟩,
    fun T => ⟨⟨T.H_mem, T.H_selfAdjoint, T.K_mem⟩, fun a => ?_, T.norm_gen_le,
      fun Z c hc => T.gen_apply_mem hc, T.star_gen_apply, T.norm_gen_apply_le_direct,
      fun hc => ⟨fun c hcS => T.gen_apply_eq_zero_of_mem_compl hc hcS,
        fun Q c => ⟨T.gen_apply_eq_gen_sub hc Q c, T.norm_gen_apply_le hc Q c⟩⟩⟩⟩
  · simp only [LindbladTerm.gen_apply, derivation_apply, LindbladTerm.jump_apply]
  · simp only [LindbladTerm.gen_apply, derivation_apply, LindbladTerm.jump_apply]

open Classical in
/-- Open systems as local generators. A Lindblad family indexed by a finite set $I$ is a family
$(T_i)_{i \in I}$ of Lindblad terms, with supports $S_i$, Hamiltonian parts $H_i$, jump
operators $\Gamma_{ij}$ and generators $L_i$, such that every sub-family is contractive:
$\|\exp(t \sum_{i \in J} L_i)\| \le 1$ for every $J \subseteq I$ and $t \ge 0$. For a Lindblad
family, its family of local generators with the direct strengths has the supports $S_i$, the
generators $L_i$ and the strengths $\kappa_i = \|H_i\| + \sum_j \|\Gamma_{ij}\|^2$. Let the net
be causal for the lattice causal index, $a \in \mathcal A(X)$, $b \in \mathcal A(Y)$, $t \ge 0$
and $A(t) = e^{tL} a$ with $L = \sum_i L_i$. With the direct strengths the walk series of the
pair $(Y, X)$ converges and $\|[A(t), b]\| \le 2\|a\|\|b\|([X \cap Y \neq \emptyset] +
\sum_{k \ge 0} \omega_k(Y, X; t))$. For every local approximation $P$ of the net, the family of
local generators with the strengths $\kappa_i = \|L_i\|$ has the supports $S_i$ and the
generators $L_i$; with these strengths the walk series of the pair $(Y, X)$ converges, the same
walk bound holds, and $\|A(t) - P_{X'} A(t)\| \le 2\|a\| \sum_{k \ge 0} \omega_k(X'^c, X; t)$ for
every region $X' \supseteq X$, this series converging as well. -/
theorem spin_lindbladFamily {Λ : Type*} {A : Type*} [CStarAlgebra A]
    {𝒜 : LinearAQFT.Net (Set Λ) A} {ι : Type*} [Fintype ι] (T : ι → LindbladTerm 𝒜) :
    ((∃ F : LindbladFamily ι 𝒜, F.term = T) ↔ ∀ (J : Finset ι) (t : ℝ), 0 ≤ t →
      ‖NormedSpace.exp (t • ∑ i ∈ J, (T i).gen)‖ ≤ 1) ∧
    ∀ F : LindbladFamily ι 𝒜,
      (∀ i, F.toGeneratorsDirect.supp i = (F.term i).supp ∧
        F.toGeneratorsDirect.L i = (F.term i).gen ∧
        F.toGeneratorsDirect.kappa i = ‖(F.term i).H‖ + ∑ j, ‖(F.term i).K j‖ ^ 2) ∧
      ∀ hc : LinearAQFT.Net.IsCausal (latticeIndex Λ) 𝒜,
        (∀ (X Y : Set Λ) (a b : A), a ∈ 𝒜 X → b ∈ 𝒜 Y → ∀ t : ℝ, 0 ≤ t →
          Summable (F.toGeneratorsDirect.walkTerm X Y t) ∧
          ‖comm (F.toGeneratorsDirect.evolve t a) b‖ ≤
            2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
              ∑' k, F.toGeneratorsDirect.walkTerm X Y t k)) ∧
        ∀ Q : LocalApprox 𝒜,
          (∀ i, (F.toGenerators hc Q).supp i = (F.term i).supp ∧
            (F.toGenerators hc Q).L i = (F.term i).gen ∧
            (F.toGenerators hc Q).kappa i = ‖(F.term i).gen‖) ∧
          (∀ (X Y : Set Λ) (a b : A), a ∈ 𝒜 X → b ∈ 𝒜 Y → ∀ t : ℝ, 0 ≤ t →
            Summable ((F.toGenerators hc Q).walkTerm X Y t) ∧
            ‖comm ((F.toGenerators hc Q).evolve t a) b‖ ≤
              2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
                ∑' k, (F.toGenerators hc Q).walkTerm X Y t k)) ∧
          ∀ X X' : Set Λ, X ⊆ X' → ∀ a ∈ 𝒜 X, ∀ t : ℝ, 0 ≤ t →
            Summable ((F.toGenerators hc Q).walkTerm X X'ᶜ t) ∧
            ‖(F.toGenerators hc Q).evolve t a - Q.P X' ((F.toGenerators hc Q).evolve t a)‖ ≤
              2 * ‖a‖ * ∑' k, (F.toGenerators hc Q).walkTerm X X'ᶜ t k := by
  refine ⟨⟨?_, fun h => ⟨⟨T, h⟩, rfl⟩⟩, fun F => ⟨fun i => ⟨rfl, rfl, rfl⟩, fun hc => ⟨
    fun X Y a b ha hb t ht => ⟨F.toGeneratorsDirect.summable_walkTerm X Y ht,
      F.liebRobinson_walk_direct hc X Y ha hb ht⟩,
    fun Q => ⟨fun i => ⟨rfl, rfl, rfl⟩,
      fun X Y a b ha hb t ht => ⟨(F.toGenerators hc Q).summable_walkTerm X Y ht,
        F.liebRobinson_walk hc Q X Y ha hb ht⟩,
      fun X X' hXX' a ha t ht => ⟨(F.toGenerators hc Q).summable_walkTerm X X'ᶜ ht,
        F.norm_sub_P_evolve_le hc Q hXX' ha ht⟩⟩⟩⟩⟩
  rintro ⟨F, rfl⟩
  exact F.contraction

/-- A dephasing term is contractive. Let $A$ be a nontrivial C*-algebra and $\Gamma \in A$
self-adjoint with $\Gamma^2 = 1$. For every real $t$ and every $a \in A$,
$e^{t \Delta_\Gamma} a = \frac{1 + e^{-2t}}{2} a + \frac{1 - e^{-2t}}{2} \Gamma a \Gamma$,
and $\|e^{t \Delta_\Gamma}\| \le 1$ for $t \ge 0$. -/
theorem spin_dephasing {A : Type*} [CStarAlgebra A] [Nontrivial A] {K : A} (hK : star K = K)
    (hK2 : K * K = 1) :
    (∀ a : A, LindbladTerm.jump K a =
      star K * a * K - (2 : ℂ)⁻¹ • (star K * K * a) - (2 : ℂ)⁻¹ • (a * (star K * K))) ∧
    (∀ (t : ℝ) (a : A), NormedSpace.exp (t • LindbladTerm.jump K) a =
      ((1 + Real.exp (-2 * t)) / 2) • a + ((1 - Real.exp (-2 * t)) / 2) • (K * a * K)) ∧
    ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp (t • LindbladTerm.jump K)‖ ≤ 1 :=
  ⟨LindbladTerm.jump_apply K, LindbladTerm.exp_smul_jump_apply hK hK2,
    fun _ ht => LindbladTerm.norm_exp_smul_jump_le_one hK hK2 ht⟩

/-! ## Harmonic bosons: the lattice phase space and the bosonic net

Throughout this section $\Lambda$ is a finite set of sites. A phase-space vector is a real
function $f$ on the coordinates $\Lambda \times \{0, 1\}$: $f(x, 0) = f^q_x$ is the position and
$f(x, 1) = f^p_x$ the momentum coordinate at the site $x$. The phase space $V$ is the real vector
space of these functions, and $\mathrm{CCR}(V, \sigma)$ is the CCR algebra of the symplectic form
$\sigma$ below, with its Weyl operators $W(f)$; its norm is the C*-norm. -/

open LocalityLean.Bosonic in
open scoped Matrix in
/-- The lattice phase space. For a finite set $\Lambda$ of sites the symplectic form is
$\sigma(f, g) = \sum_{x \in \Lambda} (f^q_x g^p_x - f^p_x g^q_x)$, and $\sigma(f, g) = f \cdot
\Omega g$ (dot product with the matrix-vector product), where the real matrix $\Omega$ on
$\Lambda \times \{0, 1\}$ has the entries $\Omega_{(x, 0), (x, 1)} = 1$ and
$\Omega_{(x, 1), (x, 0)} = -1$ for every site $x$, all other entries being $0$. A phase-space
vector $f$ is supported in a set $X$ of sites when $f(x, 0) = f(x, 1) = 0$ for every site
$x \notin X$. -/
theorem bos_phase_space {Λ : Type*} [Fintype Λ] [DecidableEq Λ] :
    (∀ f g : Λ × Fin 2 → ℝ,
      sigma Λ f g = ∑ x, (f (x, 0) * g (x, 1) - f (x, 1) * g (x, 0))) ∧
    (∀ f g : Λ × Fin 2 → ℝ, sigma Λ f g = f ⬝ᵥ (Omega Λ *ᵥ g)) ∧
    (∀ b a : Λ × Fin 2, Omega Λ b a = if b.1 = a.1 then
      (if b.2 = 0 ∧ a.2 = 1 then 1 else if b.2 = 1 ∧ a.2 = 0 then -1 else 0) else 0) ∧
    ∀ (f : Λ × Fin 2 → ℝ) (X : Set Λ), SuppIn f X ↔ ∀ x ∉ X, f (x, 0) = 0 ∧ f (x, 1) = 0 := by
  refine ⟨sigma_apply, fun f g => ?_, fun _ _ => rfl, fun _ _ => Iff.rfl⟩
  rw [sigma, Matrix.toBilin'_apply']

open LocalityLean.Bosonic BosonicLean.Weyl in
/-- The form and the bosonic net. The symplectic form $\sigma$ is alternating,
$\sigma(f, f) = 0$, and $\sigma(f, g) = 0$ whenever $f$ is supported in $X$, $g$ is supported in
$Y$ and the sets of sites $X$ and $Y$ are disjoint. The bosonic net assigns to a set $X$ of sites
the norm closure $\mathcal A(X)$ of the star subalgebra of $\mathrm{CCR}(V, \sigma)$ generated by
the Weyl operators $W(f)$ of the phase-space vectors $f$ supported in $X$; it is causal for the
lattice causal index: for disjoint $X$ and $Y$, every element of $\mathcal A(X)$ commutes with
every element of $\mathcal A(Y)$. -/
theorem bos_weylNet {Λ : Type*} [Fintype Λ] [DecidableEq Λ] :
    (sigma Λ).IsAlt ∧
    (∀ (f g : Λ × Fin 2 → ℝ) (X Y : Set Λ), SuppIn f X → SuppIn g Y → Disjoint X Y →
      sigma Λ f g = 0) ∧
    (∀ X : Set Λ, weylNet Λ X = (StarAlgebra.adjoin ℂ
      {a | ∃ f, SuppIn f X ∧ wCCR (sigma Λ) f = a}).topologicalClosure) ∧
    LinearAQFT.Net.IsCausal (latticeIndex Λ) (weylNet Λ) :=
  ⟨sigma_isAlt, fun _ _ _ _ hf hg hXY => sigma_eq_zero_of_disjoint hf hg hXY, fun _ => rfl,
    weylNet_isCausal⟩

/-! ## The Weyl commutator -/

open LocalityLean.Bosonic BosonicLean.Weyl in
/-- The Weyl commutator. For all phase-space vectors $f$ and $g$, the Weyl operators of
$\mathrm{CCR}(V, \sigma)$ satisfy $[W(f), W(g)] = (e^{-i\sigma(f, g)} - 1)\, W(g) W(f)$, and
$\|[W(f), W(g)]\| = 2\, |\sin(\sigma(f, g)/2)| \le |\sigma(f, g)|$. -/
theorem bos_weyl_commutator {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (f g : Λ × Fin 2 → ℝ) :
    comm (wCCR (sigma Λ) f) (wCCR (sigma Λ) g) =
      (Complex.exp (((-(sigma Λ f g) : ℝ) : ℂ) * Complex.I) - 1) •
        (wCCR (sigma Λ) g * wCCR (sigma Λ) f) ∧
    ‖comm (wCCR (sigma Λ) f) (wCCR (sigma Λ) g)‖ = 2 * |Real.sin (sigma Λ f g / 2)| ∧
    ‖comm (wCCR (sigma Λ) f) (wCCR (sigma Λ) g)‖ ≤ |sigma Λ f g| :=
  ⟨comm_wCCR_eq f g, norm_comm_wCCR_eq_sin f g, norm_comm_wCCR_le f g⟩

/-! ## Quadratic generators, the flow and the dynamics

A real matrix on $\Lambda \times \{0, 1\}$ acts on phase-space vectors by the matrix-vector
product, $(K f)_b = \sum_a K_{ba} f_a$. For a real matrix $M$ over a finite index set,
$e^{M} = \sum_{n \ge 0} M^n / n!$ is the matrix exponential. -/

open LocalityLean.Bosonic in
open scoped Matrix in
/-- Quadratic generators. A real matrix $K$ on $\Lambda \times \{0, 1\}$ is a quadratic
generator exactly when $K^{\mathsf T} \Omega + \Omega K = 0$, and this holds exactly when
$\sigma(K u, v) + \sigma(u, K v) = 0$ for all phase-space vectors $u$ and $v$. -/
theorem bos_isQuadraticGenerator_iff {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (K : Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ) :
    (IsQuadraticGenerator K ↔ Kᵀ * Omega Λ + Omega Λ * K = 0) ∧
    (IsQuadraticGenerator K ↔
      ∀ u v : Λ × Fin 2 → ℝ, sigma Λ (K *ᵥ u) v + sigma Λ u (K *ᵥ v) = 0) := by
  refine ⟨Iff.rfl, fun hK => hK.sigma_mulVec_add, fun h => ?_⟩
  have h0 : Matrix.toBilin' (Kᵀ * Omega Λ + Omega Λ * K) = 0 := by
    refine LinearMap.ext₂ fun u v => ?_
    have huv := h u v
    rw [sigma, Matrix.toBilin'_apply', Matrix.toBilin'_apply'] at huv
    rw [Matrix.toBilin'_apply', LinearMap.zero_apply, LinearMap.zero_apply, Matrix.add_mulVec,
      dotProduct_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec u Kᵀ, Matrix.vecMul_transpose]
    exact huv
  exact Matrix.toBilin'.injective (h0.trans (map_zero _).symm)

open LocalityLean.Bosonic in
open scoped Matrix in
/-- The flow. For a real matrix $K$ on $\Lambda \times \{0, 1\}$ the flow is the matrix
exponential $T_t = e^{tK}$, $t \in \mathbb R$; it satisfies $T_0 = 1$ and
$T_{s + t} = T_s T_t$ for all real $s$, $t$. If $K$ is a quadratic generator, every $T_t$ is
symplectic: $T_t^{\mathsf T} \Omega T_t = \Omega$, and $\sigma(T_t u, T_t v) = \sigma(u, v)$ for
all phase-space vectors $u$, $v$. -/
theorem bos_flow {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    (K : Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ) :
    (∀ t : ℝ, flow K t = NormedSpace.exp (t • K)) ∧ flow K 0 = 1 ∧
    (∀ s t : ℝ, flow K (s + t) = flow K s * flow K t) ∧
    (IsQuadraticGenerator K → ∀ t : ℝ, (flow K t)ᵀ * Omega Λ * flow K t = Omega Λ ∧
      ∀ u v : Λ × Fin 2 → ℝ, sigma Λ (flow K t *ᵥ u) (flow K t *ᵥ v) = sigma Λ u v) :=
  ⟨fun _ => rfl, flow_zero K, flow_add K, fun hK t => ⟨hK.flow_symplectic t, hK.sigma_flow t⟩⟩

open LocalityLean.Bosonic BosonicLean.Weyl in
open scoped Matrix in
/-- The dynamics. Let $K$ be a quadratic generator with flow $T_t$. For every real $t$ the
dynamics $\alpha_t$ is a ($\mathbb C$-linear) star automorphism of $\mathrm{CCR}(V, \sigma)$ with
$\alpha_t(W(f)) = W(T_t f)$ for every phase-space vector $f$, and it is the only star
automorphism with this property. Moreover $\alpha_0$ is the identity and
$\alpha_{s + t} = \alpha_s \circ \alpha_t$ for all real $s$, $t$. -/
theorem bos_alpha {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {K : Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ} (hK : IsQuadraticGenerator K) :
    (∀ (t : ℝ) (f : Λ × Fin 2 → ℝ),
      alpha hK t (wCCR (sigma Λ) f) = wCCR (sigma Λ) (flow K t *ᵥ f)) ∧
    (∀ (t : ℝ) (β : CCR (sigma Λ) ≃⋆ₐ[ℂ] CCR (sigma Λ)),
      (∀ f, β (wCCR (sigma Λ) f) = wCCR (sigma Λ) (flow K t *ᵥ f)) → β = alpha hK t) ∧
    alpha hK 0 = StarAlgEquiv.refl (R := ℂ) (A := CCR (sigma Λ)) ∧
    ∀ s t : ℝ, alpha hK (s + t) = (alpha hK t).trans (alpha hK s) := by
  have hcont : ∀ γ : CCR (sigma Λ) ≃⋆ₐ[ℂ] CCR (sigma Λ), Continuous γ := fun γ =>
    (NonUnitalStarAlgHom.instContinuousLinearMapClassComplex
      (F := CCR (sigma Λ) ≃⋆ₐ[ℂ] CCR (sigma Λ))).map_continuous γ
  have hext : ∀ γ δ : CCR (sigma Λ) ≃⋆ₐ[ℂ] CCR (sigma Λ),
      (∀ f, γ (wCCR (sigma Λ) f) = δ (wCCR (sigma Λ) f)) → γ = δ := by
    intro γ δ h
    have hW : Set.EqOn γ.toAlgEquiv.toLinearMap δ.toAlgEquiv.toLinearMap
        (Set.range (CCR.weylSystem (sigma Λ) sigma_isAlt).W) := by
      rintro _ ⟨u, rfl⟩
      exact h u
    have hcl := (LinearMap.eqOn_span' hW).closure (hcont γ) (hcont δ)
    exact StarAlgEquiv.ext fun y => hcl (weyl_mem_closure_span _ sigma_isAlt y)
  refine ⟨alpha_wCCR hK, fun t β hβ => hext _ _ fun f => by rw [hβ, alpha_wCCR], ?_, ?_⟩
  · refine hext _ _ fun f => ?_
    rw [alpha_wCCR, flow_zero, Matrix.one_mulVec]
    rfl
  · intro s t
    refine hext _ _ fun f => ?_
    rw [StarAlgEquiv.trans_apply, alpha_wCCR, alpha_wCCR, alpha_wCCR, Matrix.mulVec_mulVec,
      flow_add]

/-! ## The entrywise bound

For a real matrix $K$ over a finite index set $\iota$, $|K|$ is the matrix of absolute values,
$|K|_{ba} = |K_{ba}|$. -/

/-- The entrywise exponential bound. Let $K$ be a real matrix over a finite index set $\iota$
and $t \in \mathbb R$. The entries of the matrix exponential are the sums of convergent series,
$(e^{tK})_{ba} = \sum_{n \ge 0} t^n (K^n)_{ba} / n!$, and
$|(e^{tK})_{ba}| \le (e^{|t|\,|K|})_{ba}$ for all indices $b$, $a$. -/
theorem bos_abs_exp_apply_le {ι : Type*} [Fintype ι] [DecidableEq ι] (K : Matrix ι ι ℝ) :
    (∀ b a : ι, Bosonic.absEntry K b a = |K b a|) ∧
    (∀ (t : ℝ) (b a : ι), HasSum (fun n : ℕ => t ^ n / (n.factorial : ℝ) * (K ^ n) b a)
      (NormedSpace.exp (t • K) b a)) ∧
    ∀ (t : ℝ) (b a : ι),
      |NormedSpace.exp (t • K) b a| ≤ NormedSpace.exp (|t| • Bosonic.absEntry K) b a :=
  ⟨fun _ _ => rfl, Bosonic.hasSum_exp_apply K, Bosonic.abs_exp_apply_le K⟩

/-- Range and row sums. Let $K$ be a real matrix over a finite index set $\iota$,
$s : \iota \to \Lambda$ a map to a set of sites, $d$ a real function of two sites and
$R, v \in \mathbb R$. The matrix $K$ has range $R$ for $s$ and $d$ exactly when $K_{ba} = 0$
for all indices $b$, $a$ with $d(s(b), s(a)) > R$, and it has row sums at most $v$ exactly when
$\sum_a |K_{ba}| \le v$ for every index $b$. -/
theorem bos_hasRange_rowSumLE_iff {ι Λ : Type*} [Fintype ι] (K : Matrix ι ι ℝ)
    (s : ι → Λ) (d : Λ → Λ → ℝ) (R v : ℝ) :
    (Bosonic.HasRange K s d R ↔ ∀ b a, R < d (s b) (s a) → K b a = 0) ∧
    (Bosonic.RowSumLE K v ↔ ∀ b, ∑ a, |K b a| ≤ v) :=
  ⟨Iff.rfl, Iff.rfl⟩

/-! ## The harmonic Lieb–Robinson bound

For a finite set $X$ of sites, $\hat X = X \times \{0, 1\}$ is the set of its coordinates, and
$\|f\|_1 = \sum_a |f_a|$ is the sum of the absolute values of all coordinates of $f$. The site
of a coordinate $(x, i)$ is $x$. -/

open LocalityLean.Bosonic BosonicLean.Weyl in
open scoped Matrix in
/-- The harmonic Lieb–Robinson bound. Let $K$ be a quadratic generator with flow $T_t$ and
dynamics $\alpha_t$, let $X$ and $Y$ be finite sets of sites, $f$ a phase-space vector supported
in $X$, $g$ one supported in $Y$, and $t \in \mathbb R$. For a coordinate $b = (y, i)$ let
$\bar b$ be the other coordinate at the same site: $(y, 1)$ for $i = 0$ and $(y, 0)$ for
$i = 1$. Then
$\|[\alpha_t(W(f)), W(g)]\| \le |\sigma(T_t f, g)| \le \sum_{b \in \hat Y} \sum_{a \in \hat X}
(e^{|t|\,|K|})_{ba}\, |f_a|\, |g_{\bar b}|$. -/
theorem bos_liebRobinson {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {K : Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ} (hK : IsQuadraticGenerator K) (t : ℝ)
    {f g : Λ × Fin 2 → ℝ} {X Y : Finset Λ} (hf : SuppIn f X) (hg : SuppIn g Y) :
    ‖comm (alpha hK t (wCCR (sigma Λ) f)) (wCCR (sigma Λ) g)‖ ≤ |sigma Λ (flow K t *ᵥ f) g| ∧
    |sigma Λ (flow K t *ᵥ f) g| ≤
      ∑ b ∈ Finset.univ.filter (fun b : Λ × Fin 2 => b.1 ∈ Y),
        ∑ a ∈ Finset.univ.filter (fun a : Λ × Fin 2 => a.1 ∈ X),
          NormedSpace.exp (|t| • absEntry K) b a * |f a| * |g (b.1, if b.2 = 0 then 1 else 0)| :=
  liebRobinson_weyl hK t hf hg

open LocalityLean.Bosonic BosonicLean.Weyl in
/-- The harmonic bound, range form. Let $d$ be a real function of two sites with $d(x, x) = 0$
and $d(x, z) \le d(x, y) + d(y, z)$ for all sites, and let $K$ be a quadratic generator with
dynamics $\alpha_t$ that has range $R$ for the site map and $d$ and row sums at most $v \ge 0$.
Let $f$ be supported in a finite set $X$ of sites, $g$ in a finite set $Y$, $t \ge 0$, and $r$ a
natural number with $n R < d(y, x)$ for all $y \in Y$, $x \in X$ and natural numbers $n < r$
(for $r \ge 1$ the case $n = 0$ requires $d(y, x) > 0$, so that $X$ and $Y$ are disjoint; for
$r = 0$ the condition is empty).
Then $\|[\alpha_t(W(f)), W(g)]\| \le \|f\|_1 \|g\|_1\, \frac{(vt)^r}{r!}\, e^{vt}$. -/
theorem bos_liebRobinson_range {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {K : Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ} (hK : IsQuadraticGenerator K) {d : Λ → Λ → ℝ}
    (hd0 : ∀ x, d x x = 0) (hd : ∀ x y z, d x z ≤ d x y + d y z) {R v : ℝ}
    (hR : HasRange K Prod.fst d R) (hv : RowSumLE K v) (hv0 : 0 ≤ v) {t : ℝ} (ht : 0 ≤ t)
    {f g : Λ × Fin 2 → ℝ} {X Y : Finset Λ} (hf : SuppIn f X) (hg : SuppIn g Y) {r : ℕ}
    (hr : ∀ y ∈ Y, ∀ x ∈ X, ∀ n < r, (n : ℝ) * R < d y x) :
    ‖comm (alpha hK t (wCCR (sigma Λ) f)) (wCCR (sigma Λ) g)‖ ≤
      (∑ a, |f a|) * (∑ b, |g b|) * ((v * t) ^ r / (r.factorial : ℝ) * Real.exp (v * t)) :=
  liebRobinson_weyl_geom hK hd0 hd hR hv hv0 ht hf hg hr

open LocalityLean.Bosonic BosonicLean.Weyl in
/-- The harmonic bound, light-cone form. Under the hypotheses of the range form ($d$ a real
function of two sites with $d(x, x) = 0$ and the triangle inequality, $K$ a quadratic generator
of range $R$ and row sums at most $v \ge 0$, $f$ supported in a finite set $X$ of sites, $g$ in a
finite set $Y$, $t \ge 0$, and $n R < d(y, x)$ for all $y \in Y$, $x \in X$, $n < r$), and for
$\mu \ge 0$ and $r \ge 1$,
$\|[\alpha_t(W(f)), W(g)]\| \le \|f\|_1 \|g\|_1\, e^{-\mu r} (e^{e^{\mu} v t} - 1)$. -/
theorem bos_liebRobinson_cone {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {K : Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ} (hK : IsQuadraticGenerator K) {d : Λ → Λ → ℝ}
    (hd0 : ∀ x, d x x = 0) (hd : ∀ x y z, d x z ≤ d x y + d y z) {R v : ℝ}
    (hR : HasRange K Prod.fst d R) (hv : RowSumLE K v) (hv0 : 0 ≤ v) {t : ℝ} (ht : 0 ≤ t)
    {μ : ℝ} (hμ : 0 ≤ μ) {f g : Λ × Fin 2 → ℝ} {X Y : Finset Λ} (hf : SuppIn f X)
    (hg : SuppIn g Y) {r : ℕ} (hr1 : 1 ≤ r)
    (hr : ∀ y ∈ Y, ∀ x ∈ X, ∀ n < r, (n : ℝ) * R < d y x) :
    ‖comm (alpha hK t (wCCR (sigma Λ) f)) (wCCR (sigma Λ) g)‖ ≤
      (∑ a, |f a|) * (∑ b, |g b|) *
        (Real.exp (-μ * r) * (Real.exp (Real.exp μ * (v * t)) - 1)) :=
  liebRobinson_weyl_cone hK hd0 hd hR hv hv0 ht hμ hf hg hr1 hr

/-! ## The harmonic chain

The chain has the sites $\{0, \dots, n - 1\}$; two sites $x$, $y$ are neighbours when
$x + 1 = y$ or $y + 1 = x$, and $\deg x$ is the number of neighbours of $x$. -/

open LocalityLean.Bosonic in
/-- The harmonic chain. Let $n$ be a natural number and $\omega, \lambda \in \mathbb R$. The
potential matrix $A$ of the chain is the real $n \times n$ matrix with
$A_{xx} = \omega^2 + \lambda \deg x$, $A_{xy} = -\lambda$ for neighbours $x$, $y$, and
$A_{xy} = 0$ otherwise. The chain generator $K$ is the real matrix on
$\{0, \dots, n - 1\} \times \{0, 1\}$ with $K_{(x, 0), (y, 1)} = -A_{xy}$,
$K_{(x, 1), (x, 0)} = 1$ and all other entries $0$, so that $(K f)^q = -A f^p$ and
$(K f)^p = f^q$. The matrix $K$ is a quadratic generator; it has range $1$ for the site map and
the distance $d(x, y) = |x - y|$; and for $\lambda \ge 0$ its row sums are at most
$\max(1, \omega^2 + 4\lambda)$. -/
theorem bos_chain (n : ℕ) (ω lam : ℝ) :
    (∀ x y : Fin n, chainPotential n ω lam x y = if x = y then ω ^ 2 +
      lam * ((Finset.univ.filter fun z : Fin n => (x : ℕ) + 1 = z ∨ (z : ℕ) + 1 = x).card : ℝ)
      else if (x : ℕ) + 1 = y ∨ (y : ℕ) + 1 = x then -lam else 0) ∧
    (∀ b a : Fin n × Fin 2, chain n ω lam b a =
      if b.2 = 0 ∧ a.2 = 1 then -chainPotential n ω lam b.1 a.1
      else if b.2 = 1 ∧ a.2 = 0 ∧ b.1 = a.1 then 1 else 0) ∧
    IsQuadraticGenerator (chain n ω lam) ∧
    HasRange (chain n ω lam) Prod.fst (fun x y : Fin n => |((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)|) 1 ∧
    (0 ≤ lam → RowSumLE (chain n ω lam) (max 1 (ω ^ 2 + 4 * lam))) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, chain_isQuadraticGenerator n ω lam, chain_hasRange_one n ω lam,
    chain_rowSumLE n ω lam⟩

open LocalityLean.Bosonic BosonicLean.Weyl in
/-- The bound for the harmonic chain. Let $K$ be the chain generator on $n$ sites with
$\omega \in \mathbb R$ and $\lambda \ge 0$, assumed to be a quadratic generator (which it is
for all $\omega$, $\lambda$), $\alpha_t$ its dynamics and $v = \max(1, \omega^2 + 4\lambda)$.
Let $f$ be supported in a finite set $X$ of sites, $g$ in a finite set $Y$, $t \ge 0$, and $r$
a natural number with $r \le |y - x|$ for all $y \in Y$ and $x \in X$. Then
$\|[\alpha_t(W(f)), W(g)]\| \le \|f\|_1 \|g\|_1\, \frac{(vt)^r}{r!}\, e^{vt}$, and for
$\mu \ge 0$ and $r \ge 1$ also
$\|[\alpha_t(W(f)), W(g)]\| \le \|f\|_1 \|g\|_1\, e^{-\mu r} (e^{e^{\mu} v t} - 1)$. -/
theorem bos_chain_bound (n : ℕ) (ω : ℝ) {lam : ℝ} (hl : 0 ≤ lam)
    (hK : IsQuadraticGenerator (chain n ω lam)) {t : ℝ} (ht : 0 ≤ t)
    {f g : Fin n × Fin 2 → ℝ} {X Y : Finset (Fin n)} (hf : SuppIn f X) (hg : SuppIn g Y)
    {r : ℕ} (hr : ∀ y ∈ Y, ∀ x ∈ X, (r : ℝ) ≤ |((y : ℕ) : ℝ) - ((x : ℕ) : ℝ)|) :
    ‖comm (alpha hK t (wCCR (sigma (Fin n)) f)) (wCCR (sigma (Fin n)) g)‖ ≤
      (∑ a, |f a|) * (∑ b, |g b|) * ((max 1 (ω ^ 2 + 4 * lam) * t) ^ r / (r.factorial : ℝ) *
        Real.exp (max 1 (ω ^ 2 + 4 * lam) * t)) ∧
    ∀ μ : ℝ, 0 ≤ μ → 1 ≤ r →
      ‖comm (alpha hK t (wCCR (sigma (Fin n)) f)) (wCCR (sigma (Fin n)) g)‖ ≤
        (∑ a, |f a|) * (∑ b, |g b|) * (Real.exp (-μ * r) *
          (Real.exp (Real.exp μ * (max 1 (ω ^ 2 + 4 * lam) * t)) - 1)) := by
  have hv0 : (0 : ℝ) ≤ max 1 (ω ^ 2 + 4 * lam) := le_max_of_le_left zero_le_one
  have hr' : ∀ y ∈ Y, ∀ x ∈ X, ∀ m < r, (m : ℝ) * 1 < chainDist n y x := by
    intro y hy x hx m hm
    have hm' : (m : ℝ) < r := by exact_mod_cast hm
    rw [mul_one]
    exact hm'.trans_le (hr y hy x hx)
  exact ⟨liebRobinson_weyl_geom hK (chainDist_self n) (chainDist_triangle n)
      (chain_hasRange_one n ω lam) (chain_rowSumLE n ω lam hl) hv0 ht hf hg hr',
    fun μ hμ hr1 => liebRobinson_weyl_cone hK (chainDist_self n) (chainDist_triangle n)
      (chain_hasRange_one n ω lam) (chain_rowSumLE n ω lam hl) hv0 ht hμ hf hg hr1 hr'⟩

/-! ## Examples

These statements show that the hypotheses of the theorems above can be met and that the
objects are not degenerate. The two-qubit net is the qudit net with sites $\Lambda = \{0, 1\}$
and the alphabet $\{0, 1\}$ at each site; $\sigma^x = \begin{pmatrix} 0 & 1 \\ 1 & 0
\end{pmatrix}$ and $\sigma^z = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$, and $\sigma^x_u$,
$\sigma^z_u$ are their single-site operators at the site $u$. -/

/-- On a finite nonempty site set, the constant function $F = 1$ with reproducing constant
$C_F = |\Lambda|$ is a decay kernel, and for every family of local generators the total
strength $K = \sum_i \kappa_i$ is an $F$-bound for it. -/
theorem witness_decay_kernel {Λ : Type*} [Fintype Λ] [Nonempty Λ] {A : Type*} [CStarAlgebra A]
    {ι : Type*} [Fintype ι] {𝒜 : LinearAQFT.Net (Set Λ) A} (G : LocalGenerators ι 𝒜) :
    ∃ K : DecayKernel Λ, (∀ x y, K.F x y = 1) ∧ K.CF = Fintype.card Λ ∧
      G.IsFBound K G.totalStrength := by
  refine ⟨⟨fun _ _ => 1, Fintype.card Λ, by exact_mod_cast Fintype.card_pos, fun _ _ => zero_le_one,
    fun x y T' => ?_⟩, fun _ _ => rfl, rfl, G.totalStrength_nonneg, fun x y => ?_⟩
  · simp only [mul_one, Finset.sum_const, nsmul_eq_mul]
    exact_mod_cast Finset.card_le_univ T'
  · rw [mul_one, LocalGenerators.totalStrength, LocalGenerators.siteMatrix]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := G.ind_le_one i x
    have h2 := G.ind_le_one i y
    have h3 := G.ind_nonneg i x
    have h4 := G.ind_nonneg i y
    have h5 := G.kappa_nonneg i
    calc G.kappa i * G.ind i x * G.ind i y ≤ G.kappa i * 1 * 1 := by gcongr
      _ = G.kappa i := by ring

open scoped Matrix.Norms.L2Operator in
/-- The qudit net and the spin dynamics are not trivial. On two qubits, $\sigma^x_1$ does not
lie in $\mathcal A(\{0\})$, and $\sigma^x_0$, $\sigma^z_0$ do not commute. There is a
Hamiltonian family on the two-qubit net with a single term, of support $\{0, 1\}$, equal to
$H = \sigma^x_0 \sigma^x_1$; for it $a = \sigma^z_0 \in \mathcal A(\{0\})$ and
$b = \sigma^z_1 \in \mathcal A(\{1\})$ commute, while $[A(t), b] \neq 0$ for some $t > 0$. -/
theorem witness_spin_two_qubit :
    Qudit.siteOp (1 : Fin 2) !![(0 : ℂ), 1; 1, 0] ∉
      Qudit.quditNet (fun _ : Fin 2 => Fin 2) ({0} : Set (Fin 2)) ∧
    Qudit.siteOp (0 : Fin 2) !![(0 : ℂ), 1; 1, 0] *
        Qudit.siteOp (0 : Fin 2) !![(1 : ℂ), 0; 0, -1] ≠
      Qudit.siteOp (0 : Fin 2) !![(1 : ℂ), 0; 0, -1] *
        Qudit.siteOp (0 : Fin 2) !![(0 : ℂ), 1; 1, 0] ∧
    ∃ Φ : Interaction Unit (Qudit.quditNet fun _ : Fin 2 => Fin 2),
      Φ.supp () = {0, 1} ∧
      Φ.term () = Qudit.siteOp (0 : Fin 2) !![(0 : ℂ), 1; 1, 0] *
        Qudit.siteOp (1 : Fin 2) !![(0 : ℂ), 1; 1, 0] ∧
      Qudit.siteOp (0 : Fin 2) !![(1 : ℂ), 0; 0, -1] ∈
        Qudit.quditNet (fun _ : Fin 2 => Fin 2) ({0} : Set (Fin 2)) ∧
      Qudit.siteOp (1 : Fin 2) !![(1 : ℂ), 0; 0, -1] ∈
        Qudit.quditNet (fun _ : Fin 2 => Fin 2) ({1} : Set (Fin 2)) ∧
      comm (Qudit.siteOp (0 : Fin 2) !![(1 : ℂ), 0; 0, -1])
        (Qudit.siteOp (1 : Fin 2) !![(1 : ℂ), 0; 0, -1]) = 0 ∧
      ∃ t : ℝ, 0 < t ∧ comm (Φ.toGenerators.evolve t (Qudit.siteOp (0 : Fin 2)
        !![(1 : ℂ), 0; 0, -1])) (Qudit.siteOp (1 : Fin 2) !![(1 : ℂ), 0; 0, -1]) ≠ 0 :=
  ⟨Qudit.TwoQubit.siteOp_one_pauliX_not_mem, Qudit.TwoQubit.siteOp_pauliX_pauliZ_not_commute,
    Qudit.TwoQubit.interaction, rfl, rfl, Qudit.isLocal_siteOp _ _, Qudit.isLocal_siteOp _ _,
    Qudit.TwoQubit.comm_obsA_obsB, Qudit.TwoQubit.exists_comm_evolve_ne_zero⟩

open scoped Matrix.Norms.L2Operator in
/-- Open systems on two qubits. There is a Lindblad family on the two-qubit net with a single
term, of support $\{0\}$, Hamiltonian part $0$ and generator $L a = \sigma^z_0 a \sigma^z_0 - a$;
so the contraction hypothesis of a Lindblad family can be met. There is a Lindblad term of
support $\{0, 1\}$ with Hamiltonian part $H = \sigma^x_0 \sigma^x_1$ and generator
$L a = i[H, a] + \sigma^z_0 a \sigma^z_0 - a$ (that is, $i[H, a] + \Delta_{\sigma^z_0} a$) such
that
$[e^{tL} \sigma^z_0, \sigma^z_1] \neq 0$ for some $t > 0$. -/
theorem witness_spin_open_system :
    (∃ F : LindbladFamily Unit (Qudit.quditNet fun _ : Fin 2 => Fin 2),
      (F.term ()).supp = {0} ∧ (F.term ()).H = 0 ∧ ∀ a : Qudit.QuditAlgebra fun _ : Fin 2 => Fin 2,
        (F.term ()).gen a = Qudit.siteOp (0 : Fin 2) !![(1 : ℂ), 0; 0, -1] * a *
          Qudit.siteOp (0 : Fin 2) !![(1 : ℂ), 0; 0, -1] - a) ∧
    ∃ T : LindbladTerm (Qudit.quditNet fun _ : Fin 2 => Fin 2),
      T.supp = {0, 1} ∧
      T.H = Qudit.siteOp (0 : Fin 2) !![(0 : ℂ), 1; 1, 0] *
        Qudit.siteOp (1 : Fin 2) !![(0 : ℂ), 1; 1, 0] ∧
      (∀ a : Qudit.QuditAlgebra fun _ : Fin 2 => Fin 2, T.gen a = Complex.I • comm T.H a +
        (Qudit.siteOp (0 : Fin 2) !![(1 : ℂ), 0; 0, -1] * a *
          Qudit.siteOp (0 : Fin 2) !![(1 : ℂ), 0; 0, -1] - a)) ∧
      ∃ t : ℝ, 0 < t ∧ comm (NormedSpace.exp (t • T.gen)
        (Qudit.siteOp (0 : Fin 2) !![(1 : ℂ), 0; 0, -1]))
          (Qudit.siteOp (1 : Fin 2) !![(1 : ℂ), 0; 0, -1]) ≠ 0 := by
  refine ⟨⟨Qudit.TwoQubit.dephasingFamily, rfl, rfl, fun a => ?_⟩,
    Qudit.TwoQubit.dephasingTerm, rfl, rfl, fun a => ?_, Qudit.TwoQubit.exists_comm_exp_ne_zero⟩
  · change Qudit.TwoQubit.dephasingOnly.gen a = _
    rw [Qudit.TwoQubit.dephasingOnly_gen, LindbladTerm.jump_apply, Qudit.TwoQubit.star_obsA,
      Qudit.TwoQubit.obsA_mul_obsA, one_mul, mul_one]
    change _ = Qudit.TwoQubit.obsA * a * Qudit.TwoQubit.obsA - a
    module
  · rw [LindbladTerm.gen_apply, derivation_apply]
    change _ + ∑ _j : Fin 1, LindbladTerm.jump Qudit.TwoQubit.obsA a = _
    rw [Fin.sum_univ_one]
    rw [LindbladTerm.jump_apply, Qudit.TwoQubit.star_obsA, Qudit.TwoQubit.obsA_mul_obsA, one_mul,
      mul_one]
    change _ = _ + (Qudit.TwoQubit.obsA * a * Qudit.TwoQubit.obsA - a)
    congr 1
    module

open LocalityLean.Bosonic BosonicLean.Weyl in
/-- Two Weyl operators that do not commute. On a single site, for the phase-space vectors
$f$ with $f^q = \pi$, $f^p = 0$ and $g$ with $g^q = 0$, $g^p = 1$, one has
$\sigma(f, g) = \pi$ and $\|[W(f), W(g)]\| = 2$. -/
theorem witness_bos_weyl_noncommuting :
    sigma (Fin 1) (Pi.single (0, 0) Real.pi) (Pi.single (0, 1) 1) = Real.pi ∧
    ‖comm (wCCR (sigma (Fin 1)) (Pi.single (0, 0) Real.pi))
      (wCCR (sigma (Fin 1)) (Pi.single (0, 1) 1))‖ = 2 := by
  have hs : sigma (Fin 1) (Pi.single (0, 0) Real.pi) (Pi.single (0, 1) 1) = Real.pi := by
    rw [sigma_apply]
    simp
  refine ⟨hs, ?_⟩
  rw [norm_comm_wCCR_eq_sin, hs, Real.sin_pi_div_two, abs_one, mul_one]

open LocalityLean.Bosonic BosonicLean.Weyl in
/-- Coupled momenta in the harmonic chain. Let $K$ be the chain generator on $n + 2$ sites with
$\omega \in \mathbb R$ and coupling $\lambda > 0$, assumed to be a quadratic generator (which
it is), and $\alpha_t$ its dynamics. For the momentum unit vectors $f = \delta_{(0, 1)}$ at
the site $0$ and $g = \delta_{(1, 1)}$ at the site $1$ there is a time $t > 0$ with
$[\alpha_t(W(f)), W(g)] \ne 0$. -/
theorem witness_bos_chain_noncommuting (n : ℕ) (ω : ℝ) {lam : ℝ} (hl : 0 < lam)
    (hK : IsQuadraticGenerator (chain (n + 2) ω lam)) :
    ∃ t : ℝ, 0 < t ∧
      comm (alpha hK t (wCCR (sigma (Fin (n + 2))) (Pi.single (0, 1) 1)))
        (wCCR (sigma (Fin (n + 2))) (Pi.single (1, 1) 1)) ≠ 0 := by
  obtain ⟨t, ht, h⟩ := exists_comm_alpha_ne_zero (n + 2) ω lam (by omega) hl
  have h0 : (⟨0, by omega⟩ : Fin (n + 2)) = 0 := Fin.ext (by simp)
  have h1 : (⟨1, by omega⟩ : Fin (n + 2)) = 1 := Fin.ext (by simp)
  refine ⟨t, ht, ?_⟩
  simp only [h0, h1] at h
  exact h

end Sealed
