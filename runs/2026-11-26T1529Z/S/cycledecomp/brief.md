# Brief: Erdős Problem 184 / Erdős–Gallai cycle decomposition (read BRIEF_COMMON.md first)

Source 1, erdosproblems.com problem 184, verbatim:
"Any graph on $n$ vertices can be decomposed into $O(n)$ many edge-disjoint cycles and edges."

Source 2, manuscript "A linear cycle and edge decomposition of every graph" (OpenAI, 2026-09-24), verbatim:
"Here and throughout, a cycle is simple and has length at least three."
"Theorem 1.1. There is an absolute constant C>0 such that, for every finite simple undirected graph
G with n vertices, E(G) has a partition into at most Cn parts, each of which is the edge set of a
cycle or consists of a single edge."
"The parts in this theorem may share vertices. They share no edges, and every edge of G occurs in
exactly one part. Isolated vertices need not be covered, and the empty partition is permitted when
E(G)=\varnothing."

Use Mathlib's `SimpleGraph` and its walks/cycles where they fit.
Write your file to: runs/2026-11-26T1529Z/S/cycledecomp/reading.lean
