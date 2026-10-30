# Superspecial curves and abelian varieties via theta constants

This folder contains research code built on `Hecke.RiemannSurfaces`. It is not part of the Hecke package.
It is run with the Hecke checkout as the project:

```
cd examples/Superspecial
julia -p 4 --project=../.. run_bfs.jl 7 5            # p g [k = 8] [test = true]
```

## Contents

| file | content |
|---|---|
| `gluing_prototype.jl` | gluing along 2-torsion over any field (Igusa transformation and halving formula) and exact genus-g reconstruction (Prym/Schottky–Jung, Fay kernels, quadrics) |
| `gluing_prototype_verify.jl` | smoothness of a reconstructed genus-5 curve with Singular (separate environment) |
| `superspecial.jl` | supersingular Legendre curves, Jacobian test of a theta null point (`test_vertex!`), Hasse–Witt and Cartier–Manin, mass formula, Humbert and hyperelliptic controls; also the earlier random walk |
| `signs_fix.jl` | sign correction for points with vanishing theta constants (`correct_signs_exact3!`) |
| `superspecial_bfs.jl` | complete enumeration: neighbour tables and kernel, isomorphism keys, BFS, #Aut, mass check, worker processes, text checkpoints, parallel Jacobian tests |
| `run_bfs.jl` | driver: the enumeration (and optionally the tests) |
| `test_bfs.jl` | driver: the Jacobian tests of an enumeration, in parallel |
| `verify_hit.jl` | independent checks of a Jacobian found |
| `sp_equiv.jl` | exact test whether two θ⁸ vectors are equivalent under the affine action of Sp(2g, Z) (diagnostics) |
| `cluster/` | scripts for the Elwetritsch cluster (SLURM) |

`superspecial.jl` uses the Thomae functions of `src/RieSrf/Reconstruction/Thomae.jl`.

## Method

The (2,…,2)-isogeny graph on principally polarized superspecial abelian g-folds is connected, and
(2,…,2)-isogenies are prime to p. So a breadth-first search from E^g with E supersingular finds every
class. Each class is tested for being a Jacobian by the exact reconstruction.

- **Neighbours:** for every Lagrangian G ⊂ GF(2)^{2g}, θ_{A/G}² comes from the gluing formula.
  - The source characteristics and 8th roots of unity of Igusa's formula are tabulated once per
    Lagrangian (75 735 for g = 5).
  - Each neighbour then costs 2^g products and 2^g Walsh–Hadamard transforms.
- **Classes:** keyed by the multiset of θ⁸ = (θ²)⁴ over the even characteristics. No signs are needed for
  this.
  - **Scale:** fixed by a Bézout combination of power sums, both with multiplicities and over distinct
    values. On superspecial points the θ⁸ take very few values (for p = 11 essentially c·μ₁₅), so
    normalizing a power v^j would lose information.
  - **Frobenius:** the key is minimized over the Frobenius conjugates. A class and its conjugate can have
    Sp-equivalent θ⁸ vectors: at g = 4, p = 11 there is such a pair with #Aut = 288, and `sp_equiv.jl`
    confirms it. So the vertices of the search are Frobenius orbits. Each orbit's size is read off from
    the Frobenius conjugates of its neighbour multiset.
- **Signs:** signed θ are computed only for classes that get expanded.
  - First the Riemann relations: stored pairs, random tetrads, and relations relative to any
    nonvanishing reference term.
  - Remaining free signs are chosen so that the dual isogeny leads back to the parent.
- **Certificate:** isogenies and their duals give N(A→B)·#Aut*(B) = N(B→A)·#Aut*(A), where
  #Aut* = #Aut / (Frobenius orbit size) and N counts Lagrangian kernels.
  - #Aut* of every vertex follows from #Aut(E^g) = #Aut(E)^g·g!.
  - The enumeration is certified when all vertices are expanded, all relations are consistent, and
    Σ 1/#Aut equals the mass formula ∏ |ζ(1−2i)|/2 · ∏ (p^i + (−1)^i).
  - If the relations are inconsistent (a key collision), `bfs!` splits keys with a finer invariant.

## Results

| g | p | Frobenius orbits | classes over F̄_p | Σ 1/#Aut = mass | Jacobians |
|---|---|---|---|---|---|
| 4 | 7 | 19 | 19 | 22819/129024 ✓ | (not tested, g = 4) |
| 4 | 11 | 172 | 215 | 8485039/497664 ✓ | (not tested, g = 4) |
| 5 | 7 | 168 | (running) | | none so far |

Random walk at g = 5, p = 11, from y² = x¹¹ − x: besides that start, it found one non-hyperelliptic
superspecial curve, which is a complete intersection of three quadrics.

- It is defined over GF(121).
- It is maximal over GF(121): it has 232 points.
- The discriminant of its net of quadrics is a line times a quartic.
- It is not trigonal, so it is not among the trigonal curves of Kudo–Harashita.

## Running

- **Workers:** `-p N` starts N worker processes, which compute the neighbours of each class. The main
  process assigns classes, computes signs and, with `test = true`, runs the Jacobian tests.
  - Threads are not used: Nemo's finite-field arithmetic crashed with several threads (segfault in
    `fq_nmod_reduce`).
  - For large runs, use `test = false` and run `test_bfs.jl` afterwards, which tests in parallel.
- **Output** (in the current directory):
  - `bfs_p{p}_g{g}.txt` and `.jacobians`: rewritten after every expansion. One line per vertex: parent,
    Lagrangian, vanishing count, signs, back check, #Aut*, Frobenius orbit size, Jacobian status and key.
  - `bfs_p{p}_g{g}.state`: the full state as a text file. It is saved every `BFS_STATE_INTERVAL` seconds
    (default 600) and at the end.
  - `bfs_p{p}_g{g}.DONE`: written when the enumeration is closed and the mass formula holds.
  - `neighbour_tables_g{g}.jls`: a cache, built in about 6 min for g = 5 and rebuilt if it was written by
    another Julia version.
- **Resume:** run the same command again in the same directory. The state file can be moved to another
  machine: the keys are recomputed on loading.
- **Time for g = 5, per class:**
  - neighbours: about 75 735 × 3–7 ms ≈ 4–8 CPU-minutes, divided over the workers;
  - signs: up to about 10 s;
  - Jacobian test: up to a minute.

  Classes with more than 100 vanishing even theta constants are close to products and are not tested
  (`many_vanishing`).
- **Estimates:**
  - g = 5, p = 7 (mass ≈ 11.26): 168 Frobenius orbits, about 6 hours with 4 workers.
  - g = 5, p = 11 (mass ≈ 10⁴, so ≳ 2·10⁴ classes): about 60–100 core-days, i.e. a few days on a 16- to
    32-core node.

## Checking hits

```
julia --project=../.. verify_hit.jl curve.txt                                   # one line of a .jacobians file
julia --project=/path/to/env-with-Singular gluing_prototype_verify.jl curve.txt   # smoothness
```

`verify_hit.jl` checks:

- that the curve is a complete intersection of genus 5;
- that the Hasse–Witt matrix is 0;
- the field generated by the coefficients;
- if that field is GF(p²): a model over it, the factorization of the discriminant of the net of quadrics,
  and #C(GF(p²)).
