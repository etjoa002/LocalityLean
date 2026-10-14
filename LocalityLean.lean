/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import LocalityLean.Core.Support
import LocalityLean.Core.Generator
import LocalityLean.Core.Duhamel
import LocalityLean.Core.Path
import LocalityLean.Core.Bound
import LocalityLean.Core.Graded
import LocalityLean.Core.SiteMatrix
import LocalityLean.Core.Decay
import LocalityLean.Core.Reverse
import LocalityLean.Core.Derivation
import LocalityLean.Qudit.Config
import LocalityLean.Qudit.SiteOp
import LocalityLean.Qudit.Relabel
import LocalityLean.Qudit.Bounds
import LocalityLean.Qudit.Witness
import LocalityLean.Approx.LocalApprox
import LocalityLean.Approx.Twirl
import LocalityLean.Approx.Truncated
import LocalityLean.Approx.Lindblad
import LocalityLean.Approx.Witness
import LocalityLean.Bosonic.Banded
import LocalityLean.Bosonic.Phase
import LocalityLean.Bosonic.Harmonic
import LocalityLean.Bosonic.Chain

/-!
# LocalityLean

Lieb-Robinson bounds for quantum lattice systems from one master lemma: a path series over a
finite family of bounded local generators satisfying locality in the argument (G1), support
closure (G2) and contraction of every sub-family (G3), on a net of local algebras.

This file imports the library's modules, in four groups: `Core`, the abstract theory on a net
of local algebras (generators, paths, the path-sum bound, closed forms, time reversal,
Hamiltonian families); `Qudit`, the spin lattice; `Approx`, local approximation and open
systems; and `Bosonic`, the harmonic instance.
-/
