# Roadmap: Expander Graphs
**Summary.** This roadmap develops the foundations of the theory of expander graphs. It builds on the existing Lean repo LeanExpanderGraph [1], which formalises results from the literature on expander graphs, most notably Ref [2]. The ultimate objective is to formalise the result that random regular graphs are good expanders with high probability.

The roadmap is divided into three layers: 
- *Finite Multidigraph foundations* the definitions and results needed to represent finite directed graphs with parallel edges, and to develop their associated random walks and spectral theory.
- *Expansion theory*  the definitions of vertex, edge and spectral expansion, together with the relationships between them.
- *Random Regular Graphs are good expanders* the probabilistic and combinatorial arguments establishing that random regular bipartite graphs, and subsequently random regular graphs, are good expanders with high probability.

The accompanying Suggested.lean file provides selected Lean definitions and headline theorem signatures. It is not intended to prescribe every intermediate definition or supporting lemma needed to complete the roadmap.

## Conventions

### Mathematical conventions

- Graphs are finite directed multigraphs unless explicitly stated otherwise.
- Parallel edges are permitted and must be counted with their multiplicities where appropriate.
- An edge $(u, v)$ is directed from $u$ to $v$.
- The neighbourhood used in this project is the outgoing neighbourhood.
- Regular directed graphs have equal in-degree and out-degree at every vertex.
- All probability statements must specify their underlying finite sample space and probability distribution.

### Formalisation principles

- Reuse existing results from Mathlib and LeanExpanderGraph wherever appropriate.
- Avoid duplicating existing definitions and results without a mathematical or architectural reason.
- Supporting lemmas, intermediate definitions and API refinements are left to the implementing agent unless explicitly identified as mathematical milestones.
- The definitions and theorem signatures in Suggested.lean are indicative interfaces, not an exhaustive inventory of the required formalisation.
- Mathematical hypotheses and constants should follow the cited source results. Any generalisation or change of conventions must be justified.
- All developments should compile against the Lean toolchain and dependency revisions pinned by the repository.

## Layer 1: Finite Multidigraph Foundations

The purpose of this layer is to establish the graph-theoretic and linear-algebraic foundations required for the subsequent theory of expansion.

### 1.1  Multidigraphs, degree and regularity

Develop a representation of finite directed multigraphs which permits parallel edges.

The formalisation should cover:

- Finite vertex and edge sets.
- An edge map assigning an ordered pair of endpoints to each edge.
- Incoming and outgoing edges.
- In-degree and out-degree.
- Regular directed multidigraphs, where every vertex has equal in-degree and out-degree.
- The representation should preserve edge multiplicities. Distinct edges with identical endpoints must remain distinguishable.

### 1.2 Neighbourhoods and cuts

Develop the neighbourhood constructions required for the expansion definitions.

The formalisation should distinguish between:

- The set of distinct outgoing neighbours of a vertex or vertex set.
- Multiset neighbourhoods, where multiplicities are retained.
- Directed edges leaving a vertex subset.
- Directed edges between two specified vertex subsets.
- The distinction between set cardinality and edge multiplicity is important for the subsequent expansion arguments.

### 1.3 Adjacency matrices and random walk matrices

Define the adjacency matrix of a finite multidigraph, with entries counting the number of directed edges between each ordered pair of vertices.

Develop the relationship between:

- Adjacency matrix row sums and out-degree.
- Adjacency matrix column sums and in-degree.
- Regularity and the corresponding matrix properties.
- Define the random-walk transition matrix by normalising the adjacency matrix by the out-degree.

Establish the fundamental properties of this matrix, particularly for regular directed graphs.

### 1.4 Spectral gap

Define the spectral gap using the contraction of the random walk towards the uniform distribution in the 
$L2$ metric, following the definition of $\lambda(G)$ in Ref [2, Section 4.1.2].

The development should establish that the definition is mathematically meaningful under the appropriate hypotheses, including:

- Nonempty finite vertex sets.
- Positive regular degree.
- Existence of the relevant supremum.
- The bounds on the contraction factor and spectral gap.
- The relationship between contraction of probability distributions and the corresponding mean-zero L2 operator formulation.

The spectral gap should provide the foundation for the definition of spectral expansion in Layer 2.

## Layer 2: Expansion Theory

The purpose of this layer is to formalise the principal notions of expansion and establish the mathematical relationships between them.

The principal reference is [2, Sections 4.1.1–4.1.3].

### 2.1 Vertex Expansion

Define vertex expansion, as in Ref [2, Def 4.1], in terms of the growth of outgoing neighbourhoods of sufficiently small vertex subsets. The formalisation should support the general parameters, rather than only one particular choice.

### 2.2 Edge Expansion

Define edge expansion, as in Ref [2, Def 4.13], in terms of the number of directed edges leaving a sufficiently small vertex subset. 

Parallel edges must be counted with their multiplicities.

The regularity assumptions and the precise definition of the directed boundary must be made explicit.

### 2.3 Spectral Expansion

Define spectral expansion, as in Ref [2, Def 4.5], in terms of the spectral gap from Layer 1.

### 2.4 Relationships Between Expansion Notions

The principal objective is to establish the relationships between vertex, edge and spectral expansion.

The headline results include:

- *Spectral expansion implies vertex expansion.* Ref [2, Theorem 4.6].
- *Vertex expansion implies spectral expansion.* Ref [2, Theorem 4.9]. The intended result is that a regular graph with sufficiently strong vertex expansion has a positive spectral gap. The precise hypotheses and quantitative dependence should follow the source theorem.
- *Spectral expansion implies edge expansion.* Ref [2, Theorem 4.14(1)].
- *Edge expansion implies spectral expansion under an appropriate self-loop condition.* Ref [2, Theorem 4.14(2)]. The self-loop hypothesis is essential to the stated result and must not be omitted.
- *Expander mixing lemma.* Ref [2, Lemma 4.15]. Formalise the relationship between the number of edges between two vertex subsets and the product of their relative sizes, with an error controlled by the spectral expansion parameter.

These results should be formalised with their precise hypotheses. They should not be treated as unrestricted equivalences.

## Layer 3: Random regular graphs are good expanders

The purpose of this layer is to establish the existence of good expanders through probabilistic constructions.

The principal mathematical reference for random regular bipartite graphs being good expanders is Ref [1, Section 5.1]

The principal mathematical reference for random regular graphs being good expanders is Ref [2, Theorem 4.2]

The probabilistic foundations required for these results form part of this layer. A separate general-purpose probability library is not an objective of this roadmap.

### 3.1 Random regular bipartite graphs are good expanders

The first objective is to establish the bipartite random graph result.

Following Ref [1 Section 5.1], consider a bipartite multigraph with: N vertices in the left part. N vertices in the right part.
Every left vertex having degree D, counted with multiplicity. No restriction that the right vertices have equal degrees.

The objective is to prove that there is a positive expansion parameter α, for the appropriate degree and sufficiently large 
N, such that the resulting random bipartite multigraph is a vertex expander with probability at least 1/2.

The existing construction in ```Suggested.lean```, using ```Ω```, ```allM```, ```allGraphs``` and ```allGraphsH```, provides a starting point for this development.

In particular, the probability statement should be interpreted with respect to the finite sample space of the construction. If uniformity over the function tuples and uniformity over distinct resulting graphs are used interchangeably, the required correspondence must be justified.

### 3.2 Random regular graphs are good expanders

The second objective is to establish the corresponding result for general random regular graphs.

Following Ref [2, Theorem 4.2], the intended result is that for every integer degree D≥3, there is a positive constant α such that, for sufficiently large admissible N, a uniformly random D-regular undirected graph on N vertices is a vertex expander with probability at least 1/2.

The formalisation should specify the random regular graph model precisely, including the treatment of parallel edges and the probability distribution.

The choice of construction and proof strategy is left to the implementing agent, subject to establishing the stated mathematical result.

This result should be treated as a distinct milestone from the bipartite construction in Section 3.1.

## Scope and ownership

This roadmap owns the targets stated above. Further results in the theory of expander graphs that are left to future roadmap(s) include:

- Cayley graph constructions.
- Zig-zag products.
- Explicit algebraic constructions such as Ramanujan graph constructions.
- Applications of expander graphs.
- Advanced pseudorandomness and derandomisation theory.

## Exact supplier contracts

### From Mathlib

The development should make use of existing Mathlib facilities wherever possible.

The principal areas of Mathlib likely to be relevant are:

- Finite combinatorics: Finset, Fintype, finite functions, powersets and cardinality.
- Linear algebra: matrices, finite-dimensional vector spaces, inner products and operator norms.
- Real analysis: norms, inequalities, suprema, convergence and real-valued bounds.
- Graph theory: existing finite graph and multigraph-related constructions where applicable.
- Probability: finite probability distributions, independence, expectations and probability inequalities.
- Enumerative combinatorics: binomial coefficients, finite sums, products and counting arguments.

These are indicative dependency areas, not a requirement to introduce new abstractions or imports. Contributors should first identify and reuse existing Mathlib results.

The repository's pinned Mathlib revision is authoritative. Any proposed dependency or API should be checked against that revision.

## References
[1] https://github.com/sjh227/LeanExpanderGraph 

[2] https://people.seas.harvard.edu/%7Esalil/cs225/spring09/lecnotes/Chap4.pdf

