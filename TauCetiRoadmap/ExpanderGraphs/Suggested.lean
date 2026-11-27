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

open Multiset List

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

/-! ## Layer 1: Expansion Theory -/

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
a `(|G| / 2, 1 + γ)` spectral expander -/
theorem SpectralImpliesVertexCor {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (G : MultiDiGraph V E) (hV: 0 < #G.vertices )
    (r : ℕ) (hr : 0 < r) (hr1 : G.isRegularOfDegree r) :
    ∀ γ : ℝ, (γ ∈ Set.Ioc 0 1) ∧ (spectralExpander γ G)
        → vertexExpander (1/2 * (#G.vertices : ℝ ) ) (1 + γ) G := by
  sorry

/-- The expander mixing lemma relating spectral expansion to edge expansion. -/
lemma ExpanderMixingLemma {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (G : MultiDiGraph V E) (hV: 0 < #G.vertices ) (r : ℕ)
    (hr : 0 < r ∧ G.isRegularOfDegree r) (γ : ℝ) (hγ : spectralExpander γ G) :
    ∀ S ⊆ G.vertices, ∀ T ⊆ G.vertices, |((MultiDiGraph.eST G S T) : ℝ)
        / (#(G.vertices)*(r : ℝ)) - ((#S : ℝ) / (#G.vertices : ℝ))
        * ((#T : ℝ) / (#G.vertices : ℝ))| ≤ (1 - γ) * √ (((#S : ℝ) / (#G.vertices : ℝ))
        * (1- ((#S : ℝ) / (#G.vertices : ℝ)) ) * ((#T : ℝ) / (#G.vertices : ℝ))
        * (1- ((#T : ℝ) /(#G.vertices : ℝ)) )) := by
  sorry

/-- Non-zero spectral expansion implies non-zero edge expansion-/
lemma SpectralImpliesEdgeExpansion {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (G : MultiDiGraph V E) (hV: 0 < #G.vertices)
    (r : ℕ) (hr : 0 < r ∧ G.isRegularOfDegree r)  (γ : ℝ) (hγ : spectralExpander γ G) (hγ2 : 0 < γ):
    edgeExpander ((#G.vertices : ℝ) / 2) (γ / 2) r G := by
  sorry

/-! ## Layer 3: Random regular graphs are good expanders -/




end TauCetiRoadmap.ExpanderGraphs
