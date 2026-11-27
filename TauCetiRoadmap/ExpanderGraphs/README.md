# Roadmap: Expander Graphs
**Summary.** This roadmap develops the foundations of the theory of expander graphs. It builds on the existing Lean repo LeanExpanderGraph [1], which broadly aims to formalise the results in Ref. [2]. In particular, this roadmap builds towards the result that random regular graphs are good expanders with high probability. The roadmap is split into four layers: 
- *Finite Multidigraph foundations* the basic definitions and results needed to define directed graphs which admit parallel edges, as are the essential objects in the theory.
- *Expansion theory* definitions of the three forms of expansion, and the relationships therebetween.
- *Probabilistic foundations* serves two purposes: to allow spectral expansion to be defined in terms of convergence of a random walk on the stationary distribution, and to facilitate the construction of random graphs.
- *Random Regular Graphs and Expander Existence* the seminal result that random regular graphs are good expanders with high probability. 

## Conventions

## Layer 1: Finite Multidigraph Foundations
### 1.1  Multidigraphs, degree, regularity and neighbourhood
### 1.2 Adjacency matrices and random walk matrices
### 1.3 Spectral gap
### 1.4 Required API and Supporting Results
## Layer 2: Expansion Theory
### 2.1 Vertex Expansion
### 2.2 Edge Expansion
### 2.3 Spectral Expansion
### 2.4 Relationships Between Expansion Notions
### 2.5 Required API and Supporting Results
## Layer 3: Random regular graphs are good expanders
### 3.1 Random regular bipartite graphs are good expanders
### 3.2 Random regular graphs are good expanders
### 3.3 Required API and Supporting Results

## Scope and ownership

### Out of Scope (Recommended Future Roadmap(s))

Cayley graph constructions.
Zig-zag products.
Explicit algebraic constructions.
Ramanujan graph constructions.
Applications of expander graphs.
Advanced pseudorandomness and derandomisation theory.

## Exact supplier contracts

### From Mathlib

Mathlib dependencies.
Tau Ceti dependencies.


## References
[1] https://github.com/sjh227/LeanExpanderGraph 

[2] https://people.seas.harvard.edu/%7Esalil/cs225/spring09/lecnotes/Chap4.pdf

