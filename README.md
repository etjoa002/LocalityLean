# LocalityLean

Lieb–Robinson bounds for quantum lattice systems, formalized in Lean 4 over Mathlib.

A Lieb–Robinson bound limits how fast an observable of a quantum lattice system can influence a
distant one. For an observable `a` localized in a region `X`, evolved for a time `t` to `A(t)`,
and an observable `b` localized in a region `Y`, the commutator `‖[A(t), b]‖` is small when the
regions are far apart compared with `vt`, for a velocity `v` fixed by the interaction. The
library proves one general bound, the **path-sum bound**, for a finite family of bounded local
generators `L_i` with supports `S_i` and strengths `κ_i` on a net of local algebras:

```
‖[e^{tL} a, b]‖ ≤ 2 ‖a‖ ‖b‖ ( [X ∩ Y ≠ ∅] + Σ_{k ≥ 1} (2t)^k / k! · P_k(Y, X) ),    t ≥ 0,
```

where `L = Σ_i L_i` and `P_k(Y, X)` is the weighted count of first-contact paths of `k`
supports from `Y` to `X`. The hypotheses are locality in the argument (G1), support closure
(G2) and contraction of every sub-family (G3). Hamiltonian dynamics `A(t) = e^{itH} a e^{-itH}`
and Lindblad dynamics are instances; the published bounds for spin systems follow as
corollaries, the same bounds hold for open systems, and the local-approximation theorem turns
the bound into an approximate quantum cellular automaton. Harmonic bosons, whose Hamiltonian
is unbounded, are treated separately, by an entrywise bound on the classical propagator.

## What is proved

| | Main results | Notes |
|---|---|---|
| The path-sum bound | Nets on a lattice, causal for disjointness; local generators with (G1)–(G3); first-contact paths and their weighted count, with its recursion and the bound `P_k ≤ K^k`, `K = Σ_i κ_i`; the path-sum bound above, with the convergence of the series, and its supremum form for the commutator bound `C_{X,Y}(t)`; the graded bracket and its bound `2‖a‖‖b‖` | Ch. 1–2 |
| Closed forms | The site matrix `h_{uv} = Σ_{i: u,v ∈ S_i} κ_i` and walk weights, the domination `P_k ≤ W_k` and the walk bound; on a finite lattice the matrix form with `(e^{2th} − 1)_{yx}`; decay functions and the decay-function form `(e^{2 N C_F t} − 1)/C_F · Σ F`; bounded geometry with the form `|∂Y| (vt)^r/r! e^{vt}`, `v = 2gℓR`, and the exponential light cone; time reversal (every real `t`, with `|t|`) for negation-contractive families | Ch. 3 |
| Hamiltonians and spin lattices | Hamiltonian families satisfy (G1)–(G3), contraction by unitarity in both time directions, and their dynamics is the unitary conjugation; the role exchange `‖[A(t), b]‖ = ‖[B(−t), a]‖` and the bounds with the smaller of the two walk or kernel sums; the qudit lattice (configurations, local matrices, single-site operators, qudit interactions); the published spin-system bounds as corollaries: the matrix form (C.-F. Chen, A. Lucas and C. Yin 2023, eq. (3.36)), the decay form (B. Nachtergaele, R. Sims and A. Young 2019, Theorem 3.1) with the least `F`-bound, bounded geometry and the light cone | Ch. 4 |
| Local approximation and open systems | Local approximation of a net and ε-local maps; on the qudit lattice with cyclic alphabets, the conditional expectation onto a region as a finite twirl over clock-and-shift unitaries, its algebraic properties and `‖M − P_X M‖ ≤ N_{X^c}(M) ≤ 2‖M − P_X M‖`; the truncated dynamics and the approximate automaton for every family of local generators, and on qudits; Lindblad terms and families with both routes to (G1), their walk and truncation bounds, and the dephasing generator in closed form | Ch. 5 |
| Harmonic bosons | The CCR algebra and the Weyl relations; the lattice phase space and the bosonic net, causal; the Weyl commutator `‖[W f, W g]‖ = 2|sin(σ(f,g)/2)|`; quadratic generators, their symplectic flow and the dynamics `α_t(W f) = W(T_t f)`, a one-parameter group; the entrywise bound `|(e^{tK})_{ba}| ≤ (e^{|t||K|})_{ba}`; the harmonic bound with its range and light-cone forms; the harmonic chain | Ch. 7 |

The precise statements are the 60 theorems of [`verify/CORE.md`](verify/CORE.md), under headings
that refine the rows of this table. Conventions are listed in `CONVENTIONS.md`. Chapters 6
(fermions) and 8 (the thermodynamic limit) of the notes are still to come and carry no theorems.

## Verification

The 60 theorems of the core are 31 main results, 24 statements that describe the library's
definitions in Mathlib's terms (some with further facts), and five examples (a decay kernel and
an `F`-bound for every family on a finite lattice; a two-qubit Hamiltonian and a two-qubit open
system whose dynamics makes two commuting observables fail to commute; two Weyl operators with a
commutator of norm 2; a harmonic chain whose dynamics does the same), which show that the
hypotheses can be met and that the bounds are not about zero commutators.
`verify/Challenge.lean` states them without proofs, and `verify/Solution.lean` proves them from
the library. The command

```
lake comparator --config verify/comparator.json --paranoid
```

checks that every proved theorem has exactly the stated form, that no axioms beyond `propext`,
`Classical.choice` and `Quot.sound` are used, and that Lean's kernel and four independently
written proof checkers accept every proof. A reader who accepts the 60 statements therefore need
not read any proof. Besides the definitions described in the core, two kinds of structure are
taken from the libraries: the C*-algebra structure of the CCR algebra, a closed star subalgebra
of the bounded operators on `ℓ²(V)`, and that of the qudit algebra, whose norm is Mathlib's
operator norm of a matrix acting on the Euclidean space of complex functions on the
configurations, made available statement by statement. The same check runs on GitHub at every
change.

`lake comparator` is the proof judge maintained by the Lean developers for proofs whose author is
not trusted, including proofs produced by AI; see
[leanprover/comparator](https://github.com/leanprover/comparator) and the chapter
[Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/#validating-comparator)
of the Lean reference manual. Among its checkers are
[lean4lean](https://github.com/digama0/lean4lean) and [nanoda](https://github.com/ammkrn/nanoda_lib).
On Linux it isolates the compiled code in a sandbox; elsewhere it needs the option
`--inadvisably-no-sandbox`.

## Build and verify

With the Lean installer `elan`:

```
git clone https://github.com/etjoa002/LocalityLean
cd LocalityLean
lake exe cache get          # download the precompiled Mathlib
lake build LocalityLean
lake comparator --config verify/comparator.json --paranoid
```

The library depends on [Mathlib](https://github.com/leanprover-community/mathlib4),
[LocalAlgebrasLean](https://github.com/etjoa002/LocalAlgebrasLean) (nets of local algebras,
lattice regions, the qudit net), [LinearAQFT](https://github.com/etjoa002/LinearAQFT) (causal
indices, the symplectic net) and [BosonicLean](https://github.com/etjoa002/BosonicLean) (the CCR
algebra and its Weyl operators); their versions, and that of Lean, are fixed in
`lakefile.toml`, `lake-manifest.json` and `lean-toolchain`, and are only ever changed together.

## Methods of proof

The dynamics `e^{tL}` of a sum of bounded local generators is expanded by Duhamel's identity
from the side of the probe `b`: the terms of `L` whose support crosses the probe's region are
the perturbation; the terms inside that region vanish on the algebra of its complement, by
locality in the argument and causality, and the free term vanishes by support closure and
causality. Each step replaces the
probe by its commutator with one generator, which contraction (G3) and locality in the argument
reset to a single support; iterating gives the path series with an explicit remainder. The site
matrix dominates the path count by walks, whose sums are entries of `e^{2th}`, and the closed
forms follow from decay functions or bounded geometry. Hamiltonian dynamics is the conjugation
by `e^{itH}`, from the exponential of commuting left and right multiplications; the conditional
expectation is an average over clock-and-shift unitaries. Harmonic bosons use a different
mechanism: their dynamics is a symplectic flow on the labels of the Weyl operators, the
commutator of two Weyl operators is a phase, and the entries of the classical propagator
`e^{tK}` are bounded by those of `e^{|t||K|}`, whose range and row sums give the closed
forms.

## The notes

[`docs/lecture-notes/LocalityLean.pdf`](docs/lecture-notes/LocalityLean.pdf) gives the account
with full proofs, worked examples and numerical checks, in the chapters listed in the table
above, after a reading guide that translates between the review literature's graph language,
the interactions of mathematical physics and the generators used here. A tag beside a theorem
links to the Lean declarations that prove it; every example is marked as proved in Lean, checked
by a script, or checked on paper.

## Numerical checks

The scripts in `checks/` (Python with NumPy and SciPy; `checks/requirements.txt`) test the
statements of the notes independently of Lean: `m1a_check.py` and `path_check.py` the
path-sum bound and the path count; `m1a_crossing_check.py` the crossing-path bound `2t²` against
the exact commutator of a three-site chain, and `m1a_chain_expansion_check.py` the small-time
expansion and closed form of that commutator; `m1b_check.py` the closed forms; `m2_check.py`
Hamiltonian families and qudit lattices; `m3_check.py` the twirl, the approximation estimate,
the truncated dynamics and Lindblad terms; `long_chain.py` the twelve-qubit truncation example;
`m5_check.py` the harmonic bounds and the harmonic chain. Each script asserts what it tests and
exits nonzero at a failure; run, for example, `python -X utf8 checks/m5_check.py`. The figure
scripts `long_chain_figure.py` (from the output of `long_chain.py`) and `m5_figure.py` draw the
figures of the truncation example and of the harmonic chain and print the numbers quoted with
them.

## Library layout

`Core/` the abstract theory on a net of local algebras (generators, paths, the path-sum bound,
closed forms, time reversal, Hamiltonian families); `Qudit/` the spin lattice; `Approx/` local
approximation and open systems; `Bosonic/` the harmonic instance; `verify/` the core.

<details>
<summary>Lean files and their imports</summary>

<!-- depgraph:start -->
- **Core**
  - `Core.Bound` <- Core.Duhamel, Core.Path
  - `Core.Decay` <- Core.SiteMatrix
  - `Core.Derivation` <- Core.Reverse
  - `Core.Duhamel`
  - `Core.Generator` <- Core.Support
  - `Core.Graded` <- Core.Generator
  - `Core.Path` <- Core.Generator
  - `Core.Reverse` <- Core.Decay
  - `Core.SiteMatrix` <- Core.Bound
  - `Core.Support` <- LinearAQFT.Net.Basic, LinearAQFT.Causal.Basic
- **Qudit**
  - `Qudit.Bounds` <- Qudit.Config, Core.Derivation
  - `Qudit.Config` <- Core.Support
  - `Qudit.Relabel` <- Qudit.Config
  - `Qudit.SiteOp` <- Qudit.Config
  - `Qudit.Witness` <- Qudit.SiteOp, Qudit.Bounds
- **Approx**
  - `Approx.Lindblad` <- Approx.Truncated, Core.Derivation
  - `Approx.LocalApprox` <- Core.Generator
  - `Approx.Truncated` <- Approx.Twirl, Qudit.Bounds
  - `Approx.Twirl` <- Qudit.Config, Approx.LocalApprox, Core.Derivation
  - `Approx.Witness` <- Approx.Lindblad, Qudit.Witness
- **Bosonic**
  - `Bosonic.Banded` <- Core.Decay
  - `Bosonic.Chain` <- Bosonic.Harmonic
  - `Bosonic.Harmonic` <- BosonicLean.Weyl.System, BosonicLean.Weyl.Relabel, Bosonic.Banded, Bosonic.Phase, Core.Derivation
  - `Bosonic.Phase` <- BosonicLean.Weyl.State, LinearAQFT.Symplectic.Net, Core.Support
<!-- depgraph:end -->

</details>

## Status

The library is under development, and this repository is updated as the work progresses; see
`CONTRIBUTING.md` for problem reports and suggestions. Planned next are fermions (graded nets
and the Fock-space instance) and the thermodynamic limit (quasi-local algebras and the
infinite-volume dynamics). Candidates for later theorems, from the notes: the rescaling of units at each site for harmonic bosons, which leaves the entrywise bound
unchanged and can lower the velocity of the range form; the bounded-geometry and light-cone
forms for every real `t`, with `|t|`, for negation-contractive families; the exact row sums of
the site matrix, `Σ_{i ∋ u} κ_i |S_i|`, and of the harmonic chain; and the identification of
the least `F`-bound with the `F`-norm of B. Nachtergaele, R. Sims and A. Young (2019), when
each support carries one term.

## Citation and licence

Erickson Tjoa, *LocalityLean: Lieb–Robinson bounds for quantum lattice systems in Lean*, 2026,
https://github.com/etjoa002/LocalityLean. Apache 2.0 (`LICENSE`, `NOTICE`); `CITATION.cff` gives
the reference in machine-readable form. The reference account is C.-F. Chen, A. Lucas and
C. Yin, Rep. Prog. Phys. 86 (2023) 116001; the other sources are cited in the notes.

Developed with AI assistance. The author approved every definition and theorem statement and is
responsible for the content; every proof is checked by Lean.
