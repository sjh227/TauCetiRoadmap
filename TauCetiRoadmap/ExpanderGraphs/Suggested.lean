import Mathlib

/-!
# ExpanderGraphs: target signatures

**This file is not the roadmap.** 

This file provides compile-checked Lean interfaces for the mathematical
targets specified in `README.md`. The README is the authoritative roadmap. 
This file is a companion to it, not a replacement or a complete inventory 
of the required API.

## Conventions

* Definitions have complete implementations.
* Headline theorem statements are included with `sorry` as placeholders.
* Supporting lemmas and intermediate API declarations are left to
  contributors unless explicitly specified in the README.
* Existing Mathlib and Tau Ceti definitions and results should be reused
  wherever appropriate.
* The interfaces in this file are checked against the Lean toolchain
  and dependency revisions pinned by this repository.

See `README.md` for the mathematical scope, dependencies, references,
and remaining implementation requirements.
-/

namespace TauCetiRoadmap.ExpanderGraphs

open Multiset List


/-! ## Layer 1: Finite multidigraphs -/

/-! # 1.1 Multidigraphs, degree, and regularity -/

/-- A MultiDiGraph is a set of vertices, a set of edges,
and a map of edges to an ordered pair of vertices -/
structure MultiDiGraph (V E : Type*) where
  /-- graph vertices -/
  vertices : Finset V
  /-- graph edges -/
  edges : Finset E
  /-- map from each edge to the vertices it connects -/
  edgeMap : E → V × V
  edgesValid : ∀ e ∈ edges, edgeMap e ∈ vertices ×ˢ vertices

variable {V E : Type*}

/-- Incident outedges of a vertex are edges whose first endpoint is that vertex -/
def MultiDiGraph.incidentOutEdges [DecidableEq V]
    (G : MultiDiGraph V E) (v : V) : Finset E :=
  {e ∈ G.edges | (G.edgeMap e).fst = v}

/-- The out degree of a vertex is the cardinality of the set of incident outedges -/
def MultiDiGraph.OutDegree [DecidableEq V]
    (G : MultiDiGraph V E) (v : V) : ℕ := #(G.incidentOutEdges v)

/-- Incident inedges of a vertex are edges whose second endpoint is that vertex -/
def MultiDiGraph.incidentInEdges [DecidableEq V]
    (G : MultiDiGraph V E) (v : V) : Finset E :=
  {e ∈ G.edges | (G.edgeMap e).snd = v}

/-- The in degree of a vertex is the cardinality of the set of incident inedges -/
def MultiDiGraph.InDegree [DecidableEq V]
    (G : MultiDiGraph V E) (v : V) : ℕ := #(G.incidentInEdges v)

/-- A regular multidigraph is such that each vertex has the same in and out degree -/
def MultiDiGraph.isRegularOfDegree [DecidableEq V] (G : MultiDiGraph V E) (r : ℕ) :
    Prop := ∀ v ∈ G.vertices, (G.OutDegree v = r) ∧ (G.InDegree v = r)

/-- A graph is regular if it is regular of some degree -/
def MultiDiGraph.regular [DecidableEq V]
    (G : MultiDiGraph V E) : Prop :=
  ∃ r : ℕ, G.isRegularOfDegree r

/-! # 1.2 Neighbourhoods and cuts -/

/-- Neighbourhood: for this purposes of the present project defined as the set of
vertices connected by an out edge (nonstandard in some of the literature) -/
def MultiDiGraph.neighbourhood [DecidableEq V]
    (G : MultiDiGraph V E) (v : V) : Finset V :=
  (G.incidentOutEdges v).image fun e ↦ (G.edgeMap e).snd

/-- Neighbourhood of a set of vertices -/
def MultiDiGraph.neighbourhoodOfSet [DecidableEq V]
    (G : MultiDiGraph V E) (vs : Finset V) : Finset V := vs.biUnion G.neighbourhood

/-- A cut is the set of edges from a set of vertices to its complement -/
def MultiDiGraph.cut [DecidableEq V]
    (G : MultiDiGraph V E) (S : Finset V) : Finset E :=
  G.edges.filter (fun e =>
    let (u, v) := G.edgeMap e
    u ∈ S ∧ v ∈ G.vertices \ S)

/-- The set of edges from `S`, a subset of vertices to `T` another subset of vertices -/
def MultiDiGraph.eST [DecidableEq V]
    (G : MultiDiGraph V E) (S : Finset V) (T : Finset V) : ℕ :=
  #(G.edges.filter (fun e =>
    let (u, v) := G.edgeMap e
    u ∈ S ∧ v ∈ T))

/-- Contains the incident vertices as a multiset, so duplications are included
with the corresponding multiplicity -/
def MultiDiGraph.neighbourhood_as_multiset [DecidableEq V]
    (G : MultiDiGraph V E) (v : V) : Multiset V :=
  (G.incidentOutEdges v).val.map fun e ↦ (G.edgeMap e).snd

/-- Neighbourhood of a set of vertices taken as a multiset -/
def MultiDiGraph.neighbourhoodOfSet_as_multiset [DecidableEq V]
    (G : MultiDiGraph V E) (vs : Finset V) : Multiset V := vs.val.bind G.neighbourhood_as_multiset

/-! # 1.3 Adjacency matrices and random walk matrices -/

/-- The adjacency matrix of a multidigraph -/
def MultiDiGraph.adjacencyMatrix [DecidableEq V]
    (G : MultiDiGraph V E) : Matrix V V ℕ :=
  Matrix.of (fun u v => #{e ∈ G.edges | (G.edgeMap e).fst = u ∧ (G.edgeMap e).snd = v})

/-- The random walk matrix of an adjacency matrix is obtained by normalising the rows
by convention we place a one on the leading diagonal for all-zero rows, such that the
result is a stochastic matrix -/
noncomputable def MultiDiGraph.randomWalkMatrix [Fintype V]
    [DecidableEq V] (G : MultiDiGraph V E) : Matrix V V ℝ :=
  Matrix.of fun u v => if (∑ v, G.adjacencyMatrix u v : ℝ) = 0 then (if u = v then (1: ℝ) else
    (0: ℝ)) else (G.adjacencyMatrix u v : ℝ) / (∑ v, G.adjacencyMatrix u v : ℝ)

/-! # 1.4 Spectral gap -/

/-- Any vector of non-negative reals that sums to one is a discrete probability distribution -/
noncomputable def IsProbVector {α : Type*} (x : α → ℝ) (s : Finset α) : Prop :=
  (∑ i ∈ s, x i = 1) ∧ (∀ i ∈ s, 0 ≤ x i) ∧ (∀ i ∉ s, x i = 0)

/-- The `ℓ₂` Norm squared of a vector -/
noncomputable def L2normSQ {α : Type*} (x : α → ℝ) (s : Finset α) : ℝ :=
   ∑ i ∈ s, (x i)^2

/-- The uniform distribution over a specified set;
    note this is only meaningful for non-empty sets -/
noncomputable def UniformDist {α : Type*} (s : Finset α) : α → ℝ :=
  fun a => if a ∈ s then 1 / #s else 0

/-- The spectral gap of the random walk matrix of a MultiDiGraph -/
noncomputable def MultiDiGraph.SpectralGap [Fintype V]
    [DecidableEq V] (G : MultiDiGraph V E) : ℝ :=
  1 - sSup { y : ℝ  | ∃ p : V → ℝ , (IsProbVector p G.vertices) ∧ (p ≠ UniformDist G.vertices) ∧
    (y = √ (L2normSQ ((p ᵥ* G.randomWalkMatrix) - UniformDist (G.vertices)) G.vertices)
    / √ (L2normSQ (p - UniformDist (G.vertices)) G.vertices))}

/-! ## Layer 2: Expansion Theory -/

/-! # 2.1 Vertex Expansion -/ 

/-- Definition of vertex expansion. That `V` is Fintype not needed in the definition,
    but in practice `V` will be a Fintype for envisaged applications -/
def vertexExpander [DecidableEq V] (K : ℝ) (A : ℝ) (G : MultiDiGraph V E ) : Prop :=
  ∀ s : Finset V, s ⊆  G.vertices →
       (A * #s ≤ #(MultiDiGraph.neighbourhoodOfSet G s)) ∨ K < #s

/-! # 2.2 Edge Expansion -/

/-- Definition of edge expansion: only valid for regular graphs. That `V` is a Fintype
    not needed in the definition, but in practice `V` will be a Fintype for envisaged applications.
    `r` is intended to be the regular degree of the graph, and that property should be assumed
    when using this definition -/
def edgeExpander [DecidableEq V] (K : ℝ) (ε : ℝ) (r : ℕ) (G : MultiDiGraph V E ) : Prop :=
  ∀ s : Finset V, s ⊆  G.vertices →
      (K < #s) ∨ (( ε * (#s : ℝ) * (r)) ≤ #(G.cut s))

/-! # 2.3 Spectral Expansion -/

/-- Definition of spectral expansion : only valid for regular graphs -/
def spectralExpander [Fintype V] [DecidableEq V] (γ : ℝ) (G : MultiDiGraph V E ) :
    Prop := γ ≤ G.SpectralGap

/-! # 2.4 Relationships Between Expansion Notions -/

/-- The characteristic vector of a set of vertices-/
def CharacteristicVectorofVertexSet {V : Type*} [DecidableEq V]
    (S : Finset V) : V → ℝ :=
  fun v => if v ∈ S then 1 else 0

/-- The main theorem for spectral expansion implies vertex expansion -/
theorem SpectralImpliesVertex {V E : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq E] (G : MultiDiGraph V E) (hV: 0 < #G.vertices )
    (r : ℕ) (hr : 0 < r) (hr1 : G.isRegularOfDegree r) :
    ∀ γ : ℝ, ((γ ∈ Set.Ioc 0 1) ∧ (spectralExpander γ G)
        → ( ∀ α ∈ Set.Icc 0 1 ,
        vertexExpander (α * (#G.vertices)) (1 / ((1 - α ) * (1-γ)^2 + α ) ) G )) := by
  sorry

/-- A notable special case of `SpectralImpliesVertex`: a `γ` spectral expander is in particular
a `(|G| / 2, 1 + γ)` vertex expander -/
theorem SpectralImpliesVertexCor {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (G : MultiDiGraph V E) (hV: 0 < #G.vertices )
    (r : ℕ) (hr : 0 < r) (hr1 : G.isRegularOfDegree r) :
    ∀ γ : ℝ, (γ ∈ Set.Ioc 0 1) ∧ (spectralExpander γ G)
        → vertexExpander (1/2 * (#G.vertices : ℝ ) ) (1 + γ) G := by
  sorry

/-- Vertex expansion implies spectral expansion -/
theorem VertexImpliesSpectral {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (G : MultiDiGraph V E) (hV : 0 < #G.vertices)
    (r : ℕ) (hr : 0 < r) (hr1 : G.isRegularOfDegree r)
    (δ : ℝ) (hδ : 0 < δ)
    (hVertex : vertexExpander ((#G.vertices : ℝ) / 2) (1 + δ) G) :
    ∃ γ : ℝ, 0 < γ ∧ spectralExpander γ G := by
  sorry

/-- The expander mixing lemma relating spectral expansion to edge expansion. -/
theorem ExpanderMixingLemma {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (G : MultiDiGraph V E) (hV: 0 < #G.vertices ) (r : ℕ)
    (hr : 0 < r ∧ G.isRegularOfDegree r) (γ : ℝ) (hγ : spectralExpander γ G) :
    ∀ S ⊆ G.vertices, ∀ T ⊆ G.vertices, |((MultiDiGraph.eST G S T) : ℝ)
        / (#(G.vertices)*(r : ℝ)) - ((#S : ℝ) / (#G.vertices : ℝ))
        * ((#T : ℝ) / (#G.vertices : ℝ))| ≤ (1 - γ) * √ (((#S : ℝ) / (#G.vertices : ℝ))
        * (1- ((#S : ℝ) / (#G.vertices : ℝ)) ) * ((#T : ℝ) / (#G.vertices : ℝ))
        * (1- ((#T : ℝ) /(#G.vertices : ℝ)) )) := by
  sorry

/-- Non-zero spectral expansion implies non-zero edge expansion-/
theorem SpectralImpliesEdgeExpansion {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (G : MultiDiGraph V E) (hV: 0 < #G.vertices)
    (r : ℕ) (hr : 0 < r ∧ G.isRegularOfDegree r)  (γ : ℝ) (hγ : spectralExpander γ G) (hγ2 : 0 < γ):
    edgeExpander ((#G.vertices : ℝ) / 2) (γ / 2) r G := by
  sorry

/-- Edge expansion implies spectral expansion when every vertex has
a sufficiently large fraction of self-loops.
-/
theorem EdgeImpliesSpectralExpansion {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (G : MultiDiGraph V E) (hV : 2 < #G.vertices)
    (r : ℕ) (hr : 0 < r) (hr1 : G.isRegularOfDegree r)
    (ε α : ℝ) (hα : α ∈ Set.Icc 0 1)
    (hε : 0 ≤ ε)
    (hEdge : edgeExpander ((#G.vertices : ℝ) / 2) ε r G)
    (hSelfLoops : ∀ v ∈ G.vertices,
      α * (r : ℝ) ≤
        (((G.incidentOutEdges v).filter
          (fun e => G.edgeMap e = (v, v))).card : ℝ)) :
    spectralExpander (α * ε ^ 2 / 2) G := by
  sorry

/-! ## Layer 3: Random regular graphs are good expanders -/

/-! # 3.1 Random regular bipartite graphs are good expanders -/

/-- Prop for when a graph is bipartite with specified left part -/
def isBipartite_vleft {V E : Type*} (G : MultiDiGraph V E) (vleft : Finset V) : Prop :=
  vleft ⊆ G.vertices -- basic requirement
  ∧ (∀ u ∈ vleft, ∀ v ∈ vleft,
  ¬ (∃ e ∈ G.edges, (G.edgeMap e).fst = u ∧ (G.edgeMap e).snd = v ))
  -- no edges between vertices in the left part
  ∧ (∀ u ∉ vleft, ∀ v ∉ vleft,
  ¬ (∃ e ∈ G.edges, (G.edgeMap e).fst = u ∧ (G.edgeMap e).snd = v ))
  -- no edges between vertices in the right part

/-- Prop for when a graph is in `Bip n r` with left part specified
for convenience -/
def isBipartite_n_r_vleft {V E : Type*}  [DecidableEq V] (G : MultiDiGraph V E)
    (n : ℕ) (r : ℕ) (vleft : Finset V) : Prop :=
  #vleft = n -- size of the left part
  ∧ #G.vertices = 2 * n -- equal sized parts
  ∧ isBipartite_vleft G vleft
  ∧ ∀ u ∈ vleft, G.OutDegree u = r -- left out regular

/-- Prop for when a graph is a bipartite vertex expander-/
def isBipartiteVertexExpander {V E : Type*} [DecidableEq V]
    (G : MultiDiGraph V E) (K : ℝ) (A : ℝ)
    (vleft : Finset V)
    : Prop :=
  ∃ n : ℕ, ∃ r : ℕ, (isBipartite_n_r_vleft G n r vleft) ∧
      ∀ s ⊆ vleft, (A * #s ≤ #(MultiDiGraph.neighbourhoodOfSet G s)) ∨ K < #s

/-- Map from an array of random numbers to the corresponding left out-regular
bipartite graph -/
def Ω (n r : ℕ) (M : Fin r → Fin n → Fin n) :
    MultiDiGraph (Fin (n + n)) (Fin r × Fin n) :=
  let edges : Finset (Fin r × Fin n) := Finset.univ
  let edgeMap : (Fin r × Fin n) → (Fin (n + n) × Fin (n + n)) :=
    fun (i, j) ↦ (Fin.castAdd n j, Fin.natAdd n (M i j))
  {
    vertices := Finset.univ,
    edges := edges,
    edgeMap := edgeMap,
    edgesValid := by
      intros e he
      simp only [mem_product]
      aesop
  }


/-- All functions from Fin r to Fin n to Fin n -/
def allM (n r : ℕ) : Finset (Fin r → Fin n → Fin n) :=
  Finset.univ.image id

open Classical

/-- All graphs for all possible M, as defined in `def allM` -/
noncomputable def allGraphs (n r : ℕ) :
  Finset (MultiDiGraph (Fin (n + n)) (Fin r × Fin n)) :=
  (allM n r).image (Ω n r)

/-- The set of all graphs that satisfy the expansion condition -/
noncomputable def allGraphsH  (n r : ℕ) :
  Finset (MultiDiGraph (Fin (n + n)) (Fin r × Fin n)) :=
  {G ∈ allGraphs n r | isBipartiteVertexExpander G (n / ((Real.exp 1)^3 * r^4))
  (r-2) {i : Fin (n + n) | i < n} }

/-- At least two thirds of graphs constructed by `Ω` are
    (Θ(n), θ(r))- bipartite vertex expanders -/
theorem bipartite_vertex_expanders_exist (n r : ℕ) (hn : 1 ≤ n) (hr : 2 ≤ r):
    (2 / 3 : ℝ) ≤ (#(allGraphsH n r) : ℝ) / (#(allGraphs n r) : ℝ) := by
  sorry

/-! # 3.2 Random regular graphs are good expanders -/

/-
SKELETON for roadmap target 3.2. UNTESTED: not compiled against Mathlib.

Paste inside `namespace TauCetiRoadmap.ExpanderGraphs`, after
`bipartite_vertex_expanders_exist` and before `end TauCetiRoadmap.ExpanderGraphs`.
Relies on `MultiDiGraph`, `vertexExpander`, `isRegularOfDegree`, `adjacencyMatrix`
from earlier in Suggested.lean.
-/

/-! # 3.2 Random regular graphs are good expanders (Claude) -/

/-! ## Model: the pairing (configuration) model

Each of the `N` vertices carries `D` half-edges, so the half-edges are `Fin N × Fin D`.
A *perfect matching* of the half-edges is a fixed-point-free involution `σ`.
The graph has one arc `p → σ p` for each half-edge `p`, from the vertex of `p` to the
vertex of `σ p`. So every undirected edge `{p, σ p}` appears as two opposite arcs
(symmetric digraph). A self-loop uses two half-edges at one vertex and contributes
two arcs `v → v`, so loops count twice towards the degree and every vertex has
in- and out-degree exactly `D`. Parallel edges and loops are allowed.

The sample space is the finite set of perfect matchings of the `N * D` half-edges,
with the uniform distribution. NOTE: this induces a non-uniform distribution on the
resulting multigraphs (weighted by loops and edge multiplicities); it is not "uniform over
D-regular multigraphs". The model must match the one used in the source proof.
-/

/-- A perfect matching of a set of half-edges, as a fixed-point-free involution. -/
def IsPerfectMatching {α : Type*} (σ : Equiv.Perm α) : Prop :=
  Function.Involutive σ ∧ ∀ x, σ x ≠ x

/-- The symmetric multidigraph of a matching `σ` of the half-edges `Fin N × Fin D`;
the edge type is the set of half-edges themselves. -/
def pairingGraph (N D : ℕ) (σ : Equiv.Perm (Fin N × Fin D)) :
    MultiDiGraph (Fin N) (Fin N × Fin D) where
  vertices := Finset.univ
  edges := Finset.univ
  edgeMap := fun p => (p.1, (σ p).1)
  edgesValid := by
    intro e _
    simp

open Classical in
/-- The finite sample space: all perfect matchings of the `N * D` half-edges.
Empty unless `N * D` is even. -/
noncomputable def allPairings (N D : ℕ) : Finset (Equiv.Perm (Fin N × Fin D)) :=
  Finset.univ.filter (fun σ => IsPerfectMatching σ)

open Classical in
/-- The matchings whose graph is an `(α N, A)` vertex expander. -/
noncomputable def goodPairings (N D : ℕ) (α A : ℝ) :
    Finset (Equiv.Perm (Fin N × Fin D)) :=
  (allPairings N D).filter
    (fun σ => vertexExpander (α * (N : ℝ)) A (pairingGraph N D σ))

/-! ### Sanity lemmas (modelling API; contributors may restructure) -/

/-- Every pairing graph is `D`-regular (needs only that `σ` is a bijection). -/
theorem pairingGraph_isRegularOfDegree (N D : ℕ) (σ : Equiv.Perm (Fin N × Fin D)) :
    (pairingGraph N D σ).isRegularOfDegree D := by
  sorry

/-- A matching gives a symmetric adjacency matrix, i.e. an undirected multigraph. -/
theorem pairingGraph_adjacencyMatrix_isSymm (N D : ℕ)
    (σ : Equiv.Perm (Fin N × Fin D)) (hσ : IsPerfectMatching σ) :
    (pairingGraph N D σ).adjacencyMatrix.IsSymm := by
  sorry

/-- The sample space is nonempty exactly when `N * D` is even. -/
theorem allPairings_nonempty_iff (N D : ℕ) :
    (allPairings N D).Nonempty ↔ Even (N * D) := by
  sorry

/-! ### Headline target -/

/-- Random regular graphs are good expanders (cf. Ref [2, Theorem 4.2]).
For every `D ≥ 3` there is `α > 0` such that for all sufficiently large `N` with `N * D`
even, a uniformly random pairing gives a `(α N, D - 1.01)` vertex expander with
probability at least `1/2`.
 -/
theorem random_regular_graphs_expand (D : ℕ) (hD : 3 ≤ D) :
    ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even (N * D) →
      (1 / 2 : ℝ) ≤
        (#(goodPairings N D α ((D : ℝ) - 101 / 100)) : ℝ) / (#(allPairings N D) : ℝ) := by
  sorry

end TauCetiRoadmap.ExpanderGraphs

