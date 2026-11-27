import Mathlib

/-!
# ExpanderGraphs: target signatures

**This file is not the roadmap.** The roadmap is `README.md`. This file states the roadmap's
headline theorems against the pinned Mathlib and Tau Ceti, each with `sorry`, together with the
two definitions they need; every definition has a real body. Every headline theorem of the
README is statable at the pins and is stated here. The README's remaining targets, API lists and
Checks are not restated.

-/

namespace TauCetiRoadmap.ExpanderGraphs

variable {V : Type*}

/-! ## Layer 1: Finite multidigraphs -/

/-! # 1.1 Multidigraphs, degree, regularity and neighbourhoods -/

/-- A MultiDiGraph is a set of a vertices, a set of edges,
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

/-- All incident edges of a vertex are all edges that start or finish at that vertex -/
def MultiDiGraph.incidentAllEdges (G : MultiDiGraph V E)
    [DecidableEq V] (v : V) : Finset E :=
  {e ∈ G.edges | (G.edgeMap e).fst = v ∨ (G.edgeMap e).snd = v}

/-- The degree of a vertex is the cardinality of the set of incident edges -/
def MultiDiGraph.Degree [DecidableEq V]
    (G : MultiDiGraph V E) (v : V) : ℕ := #(G.incidentAllEdges v)

/-- A regular multidigraph is such that each vertex has the same in and out degree -/
def MultiDiGraph.isRegularOfDegree [DecidableEq V] (G : MultiDiGraph V E) (r : ℕ) :
    Prop :=
  ∀ v ∈ G.vertices, (#(G.edges.filter (fun e => (G.edgeMap e).fst = v)) = r) ∧
      (#(G.edges.filter (fun e => (G.edgeMap e).snd = v)) = r)

/-- A graph is regular if it is regular of some degree -/
def MultiDiGraph.regular [DecidableEq V]
    (G : MultiDiGraph V E) : Prop :=
  ∃ r : ℕ, G.isRegularOfDegree r

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

/-! # 1.2 Adjacency matrices and random walk matrices -/

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

/-! # 1.3 Spectral gap -/

/-- Any vector of non-negative reals that sums to one is a discrete probability distribution -/
noncomputable def IsProbVector (x : α → ℝ) (s : Finset α) : Prop :=
  (∑ i ∈ s, x i = 1) ∧ (∀ i ∈ s, 0 ≤ x i) ∧ (∀ i ∉ s, x i = 0)

/-- The `ℓ₂` Norm squared of a vector -/
noncomputable def L2normSQ (x : α → ℝ) (s : Finset α) : ℝ :=
   ∑ i ∈ s, (x i)^2

/-- The uniform distribution over a specified set;
    note this is only meaningful for non-empty sets -/
noncomputable def UniformDist (s : Finset α) : α → ℝ :=
  fun a => if a ∈ s then 1 / #s else 0

/-- The spectral gap of the random walk matrix of a MultiDiGraph -/
noncomputable def MultiDiGraph.SpectralGap [Fintype V]
    [DecidableEq V] (G : MultiDiGraph V E) : ℝ :=
  1 - sSup { y : ℝ  | ∃ p : V → ℝ , (IsProbVector p G.vertices) ∧ (p ≠ UniformDist G.vertices) ∧
    (y = √ (L2normSQ ((p ᵥ* G.randomWalkMatrix) - UniformDist (G.vertices)) G.vertices)
    / √ (L2normSQ (p - UniformDist (G.vertices)) G.vertices))}


open Multiset List






end TauCetiRoadmap.ExpanderGraphs
