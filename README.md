# Block structure and hidden vanishings of the Cartier-Manin matrix for superelliptic curves y^n = x^d + sigma x^r + 1 over F_p

Research package accompanying the article *Block Structure and Hidden Vanishings of the Cartier-Manin
Matrix for Superelliptic Curves y^n = x^d + sigma x^r + 1 over F_p* (`vanissements_yn_theory_en.pdf`,
version 4.3.1, 5 November 2026). It contains the article (PDF), the note of complete proofs it cites
(`proofs_blocks.tex` / `.pdf`), the code that checks its statements, a licence and this file.

**Author:** Mohamed Sofiene, independent researcher (mohamedsofiene@gmail.com).
Technical Head, Office National de Telediffusion de Tunisie (ONT); B.Sc. in IoT and Communication
Networks; B.Sc. in Electrical Engineering, University of Tunis.

**Archives and citation:** Zenodo [10.5281/zenodo.23857552](https://doi.org/10.5281/zenodo.23857552);
OSF [10.17605/OSF.IO/QBV8C](https://doi.org/10.17605/OSF.IO/QBV8C). See `CITATION.cff`.

**Status of the results.** Statements in the document are labelled **[D]** proved (by hand),
**[V]** checked numerically on a finite set of cases (not proved), **[O]** open. A passing script
is a numerical check of a statement on the cases it runs; it is not a proof. The document makes **no
claim of novelty**: no zbMATH/MathSciNet search was possible and several cited works were read only
through their abstracts.

## Setting in one paragraph

Over F_p (p odd, p not dividing n), for the curve y^n = f(x) = x^d + sigma x^r + 1 with gcd(d,n)=1,
the Cartier operator has block form: the block M^(k) (k = 1..n-1) has entries `[x^(p b - i)] f^N`,
`N = (k_out p - k)/n`, `k_out = k/p mod n`, `g_k = floor(k d / n)`. For a 2-cycle (k0,k1) put
`M0 = M^(k0)` (g1 x g0), `M1 = M^(k1)` (g0 x g1), `Phi = M1 M0`. A *hidden vanishing* is a case where
the support graph of Phi has a perfect matching but rank Phi < g0 for every smooth sigma.

## Requirements

* Python 3.9 or later (standard library only) for most scripts;
* `numpy` for `verify_kernel_theorem.py` and `verify_exact_forms_laws.py`;
* Sage is **not** required: `vanissements_yn.sage` and `corank_survey.sage` are also valid Python
  (they use Sage's fast finite-field linear algebra when available and a pure-Python fallback otherwise).

Run the scripts from this directory (they import `tvariant.py` as a small common library).

## Contents

| File | What it checks | Document | Time |
|---|---|---|---|
| `verify_hand_proofs.py` | Example A (`(8,3,7,2,5)`, det Phi = -9 sigma^3), Example B (`(8,3,5,1,5)`, det Phi = 2 sigma (sigma^2-1) mod 3), and every number of the by-hand proof of the mixed case `(12,23,13,10,5)` (three steps, matching, rank Phi = 4, bound also for M1 D M0 with random diagonal D) | Sec. 11, 16 | seconds |
| `verify_kernel_theorem.py [N] [seed]` | Theorem (kernel): kernel of a block = `{L_N q : deg L_N q < g}`, on N random smooth cases; prints `PASS`/mismatches | Sec. 16 | ~10 s for 3000 cases |
| `verify_recurrence_twins.py` | Recurrence lemma (exact over Z), twin-column corollary (5 of the 7 census twin-column cases are covered), examples (a) and (b) | Sec. 16 | seconds |
| `verify_exact_forms_laws.py [pmax] [dmax]` | Profile of `Im L_N`: [D] missing residue class `-1-Nd`; [V] conservation law `sum k_s = floor(Nd/p)` and p-1 classes; counts of sigma-independent profiles. Default domain p <= 7, d <= 8 | Sec. 16 | seconds (p <= 11, d <= 9: about 1 min) |
| `cut_search.py n p d r k0 [sigma]` | Rank cut: minimises `rk M1[:,S] + rk M0[S^c,:]` over subsets S (exhaustive for g1 <= 14) | Sec. 16 (rank cut) | seconds |
| `census_exact_zero.py [PMAX NMAX DMAX GMAX]` | Census of hidden vanishings with `det Phi == 0` in Z[sigma] and Menger flow = g0; default domain of the document reproduces **27 distinct cases** (11 deficient block, 13 cut, 3 without cut) | Sec. 16 | ~10 s |
| `tvariant.py [pmax] [gmax]` | Variant `y^n = x^d + sigma x^r + t` and parameters outside F_p: 59 cases with gcd(d,p-1) > 1; expected summary: 32 Z-identical cases (never lose the deficiency), 27 mod-p-only cases (14 lose it for some t that is not a d-th power) | Sec. 17 | ~30 s |
| `verify_yn_pure_python.py` | Independent check of Theorems A and B: Cartier-Manin stabilised rank versus point counting over F_{p^m}, 18 configurations; ends with `SUMMARY: 18 / 18 MATCH` | Sec. 2, 3, 5 | ~3 min |
| `vanissements_yn.sage` | All-in-one bench for a case or a sweep: blocks, ranks, Menger flow, exact det, Cauchy-Binet, common kernel of layers, fourth monomial, criterion for d = p. `python3 vanissements_yn.sage n p d r k0` or `python3 vanissements_yn.sage sweep NMAX PMAX DMAX [GMAX]` | Sec. 7-10 | seconds |
| `corank_survey.sage [PMAX NMAX DMAX GMAX]` | Corank survey outside the family p = -1 mod n; writes `corank_survey.csv` | Sec. 13 | default run is long; try `13 20 12 6` |
| `proofs_blocks.tex` | Note of complete by-hand proofs (kernel of a block, corank formula, duality law (K)) | Sec. 7 | compile with xelatex or pdflatex |
| `run_checks.sh` | Runs the fast checks above in one go | | ~1 min |

Section numbers refer to version 4.3.1 of the article.

## Quick start

```sh
sh run_checks.sh                         # fast checks
python3 verify_hand_proofs.py            # the by-hand proofs, number by number
python3 cut_search.py 12 23 13 10 5 2    # rank cut for the mixed case: best cut value 4 < g0 = 5
python3 census_exact_zero.py             # distinct cases: 27
python3 -I verify_yn_pure_python.py      # slower independent check of Theorems A and B
```

## Known limitations

* The large sweeps quoted in the document (the catalogues of 233 and 143 cases, the 6104 cases with
  d = p, the 16331 cases of the corank survey) were produced with earlier versions of the scripts; they
  are not all re-runnable one by one from this package. The package reproduces the new results of
  versions 4.1 and 4.2 and the by-hand proofs.
* Exactness over Z of `det Phi` is tested at one random sigma modulo 2^61 - 1 (probabilistic).
* Statements "for every sigma" are for sigma in F_p; outside F_p see the document (Sec. 17).
* The `.sage` files keep a few internal names (`'balayage'` was renamed `'sweep'`; dictionary keys
  were translated to English); the logic is unchanged and was checked by comparing outputs.

## Licence

MIT, see `LICENSE`. Copyright (c) 2026 Mohamed Sofiene. Change the licence if you prefer another one.

## Version 4.3 / 4.3.1 additions

- `verify_v43_checks.py` (output saved in `verify_v43_checks_output.txt`): checks the corrected worked-example matrices of Section 4 and the Fermat-type example (n,p,d,r)=(9,17,16,3), k=2, where det Phi = 8(sigma^16 - 1) mod 17 symbolically.
- `proofs_blocks.tex/pdf`: theorem numbering is Lemma 1, Th. 2 (kernel), Prop. 6, Th. 7 (corank), Th. 10 (law K), Cor. 11.
- Version 4.3.1 only changes the title and the title block of the article; the content is that of version 4.3.
- `run_checks_output.txt` is the saved output of `sh run_checks.sh` on the released files.
- `pure_python_output.txt` is the saved output of `python3 -I verify_yn_pure_python.py` (18 / 18 MATCH).
