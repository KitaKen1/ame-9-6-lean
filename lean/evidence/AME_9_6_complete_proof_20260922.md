# Explicit mixed binary–ternary phase construction of an AME(9,6) state

This document specifies a state exactly and gives a finite, exact certificate that every four-party reduced density matrix is the identity divided by 1296. The existence proof uses integer arithmetic and roots of unity. Discovery used SAT; verification does not use SAT, floating point arithmetic, an optimization tolerance, or an assumed nonexistence/existence result.

The target statement is `OpenQuantumProblem35.ame_9_6_open`, namely `ExistsAME 9 6`, in `FormalConjectures/OpenQuantumProblems/35.lean`. This is a mathematical construction and executable exact certificate. It is not a Lean kernel proof.

## 1. State and conventions

Number the nine parties by 0 through 8. At each party use the basis
\[
 |x,y\rangle:=|3x+y\rangle\in\mathbb C^6,
 \qquad x\in\{0,1\},\quad y\in\{0,1,2\}.
\]
Let \(\omega=e^{2\pi i/3}\). For a symmetric zero-diagonal matrix \(A\), write
\[
 q_A(t)=\sum_{0\le i<j\le8}A_{ij}t_it_j.
\]
The binary entries of \(G\) are interpreted modulo 2; the entries of \(B,H,C\) are interpreted modulo 3. In the mixed term, the bits \(x_i\) are the ordinary representatives 0 and 1 in \(\mathbb F_3\).

Define
\[
 \boxed{\displaystyle
 |\Psi\rangle=6^{-9/2}
 \sum_{x\in\{0,1\}^{9}}\sum_{y\in\mathbb F_3^{9}}
 (-1)^{q_G(x)}\omega^{q_C(y)+x^{\mathsf T}By+q_H(x)}
 \bigotimes_{i=0}^{8}|3x_i+y_i\rangle .}
\]

The four matrices are the following:

\[
G=\begin{pmatrix}
0 & 1 & 1 & 1 & 1 & 1 & 1 & 1 & 1\\
1 & 0 & 0 & 0 & 0 & 1 & 0 & 1 & 1\\
1 & 0 & 0 & 0 & 0 & 1 & 1 & 1 & 0\\
1 & 0 & 0 & 0 & 1 & 0 & 1 & 0 & 1\\
1 & 0 & 0 & 1 & 0 & 0 & 0 & 1 & 1\\
1 & 1 & 1 & 0 & 0 & 0 & 1 & 1 & 1\\
1 & 0 & 1 & 1 & 0 & 1 & 0 & 0 & 1\\
1 & 1 & 1 & 0 & 1 & 1 & 0 & 0 & 0\\
1 & 1 & 0 & 1 & 1 & 1 & 1 & 0 & 0
\end{pmatrix}.
\]

\[
B=\begin{pmatrix}
0 & 0 & 2 & 1 & 2 & 1 & 0 & 0 & 2\\
0 & 0 & 1 & 0 & 0 & 1 & 1 & 1 & 1\\
0 & 2 & 0 & 1 & 0 & 1 & 0 & 1 & 1\\
1 & 0 & 0 & 0 & 2 & 1 & 2 & 0 & 0\\
0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0\\
0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0\\
0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0\\
0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0\\
0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0
\end{pmatrix}.
\]

\[
H=\begin{pmatrix}
0 & 2 & 1 & 0 & 0 & 0 & 0 & 0 & 0\\
2 & 0 & 0 & 1 & 0 & 0 & 0 & 0 & 0\\
1 & 0 & 0 & 1 & 0 & 0 & 0 & 0 & 0\\
0 & 1 & 1 & 0 & 0 & 0 & 0 & 0 & 0\\
0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0\\
0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0\\
0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0\\
0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0\\
0 & 0 & 0 & 0 & 0 & 0 & 0 & 0 & 0
\end{pmatrix}.
\]

\[
C=\begin{pmatrix}
0 & 2 & 0 & 0 & 0 & 2 & 1 & 2 & 1\\
2 & 0 & 0 & 2 & 1 & 2 & 0 & 1 & 0\\
0 & 0 & 0 & 0 & 1 & 2 & 0 & 1 & 1\\
0 & 2 & 0 & 0 & 0 & 1 & 0 & 1 & 1\\
0 & 1 & 1 & 0 & 0 & 1 & 2 & 2 & 1\\
2 & 2 & 2 & 1 & 1 & 0 & 1 & 2 & 1\\
1 & 0 & 0 & 0 & 2 & 1 & 0 & 1 & 1\\
2 & 1 & 1 & 1 & 2 & 2 & 1 & 0 & 1\\
1 & 0 & 1 & 1 & 1 & 1 & 1 & 1 & 0
\end{pmatrix}.
\]

These data are also in `final_candidate_v1.json`. The SHA256 of the canonical matrix JSON is
`14592fc0c407b71335dffe00d0ffaedbcd216561bcba45043e940208fcd36e42`.

## 2. Exact marginal criterion

Fix a set \(S\) of four parties, and put \(O=\{0,\ldots,8\}\setminus S\). Consider a matrix entry of the reduced state on \(S\), with bra labels \((x,y)\) and ket labels \((x',y')\). Here these four vectors are restricted to \(S\). Let
\[
 d=x-x'\in\{-1,0,1\}^{S},\qquad e=y-y'\in\mathbb F_3^{S}.
\]
Define, for \(i\in O\),
\[
 \begin{aligned}
 \alpha_i&=\sum_{j\in S}C_{ij}e_j+
                 \sum_{j\in S}B_{ji}d_j\pmod3,\\
 r_i&=\sum_{j\in S}G_{ij}\mathbf1_{d_j\ne0}\pmod2,\\
 \beta_i&=\sum_{j\in S}B_{ij}e_j+
                \sum_{j\in S}H_{ij}d_j\pmod3.
 \end{aligned}
\]

**Lemma.** Up to a phase of modulus one that depends only on the bra and ket labels in \(S\), the reduced matrix entry is
\[
 6^{-9}\prod_{i\in O}(1+\omega^{\alpha_i}+\omega^{2\alpha_i})
          \prod_{i\in O}(1+(-1)^{r_i}\omega^{\beta_i}).
\]

**Proof.** In the partial trace the binary and ternary environment coordinates are the same in the bra and ket. Every phase term supported completely inside \(O\) therefore cancels. Terms supported completely in \(S\) contribute an overall phase. The remaining ternary environment coordinate at site \(i\) has coefficient \(\alpha_i\). Its three-value sum is \(1+\omega^{\alpha_i}+\omega^{2\alpha_i}\). The remaining binary environment coordinate has binary coefficient \(r_i\) and ternary coefficient \(\beta_i\); its two-value sum is \(1+(-1)^{r_i}\omega^{\beta_i}\). The sums separate because no term involving two environment coordinates remains. The normalization factor is \(6^{-9}\). ∎

Consequently this entry vanishes exactly when
\[
 \left(\exists i\in O:\alpha_i\ne0\right)
 \quad\text{or}\quad
 \left(\exists i\in O:r_i=1\text{ and }\beta_i=0\right).
 \tag{*}
\]
Indeed the first factor is zero exactly when \(\alpha_i\ne0\), while a second factor is zero exactly when \(r_i=1,\beta_i=0\). No approximate cancellation is involved.

## 3. Exhaustion of all entries

For every one of the \(\binom94=126\) cuts, the map
\[
 e\longmapsto C_{O,S}e\quad(\mathbb F_3^4\longrightarrow\mathbb F_3^5)
\]
is injective: the checker enumerates all 81 input vectors and obtains 81 distinct output vectors. This verifies rank 4 directly, without depending on the provenance of \(C\).

When \(d=0\) and \(e\ne0\), this injectivity implies \(\alpha\ne0\). Thus all off-diagonal entries with equal binary labels vanish.

When \(d\ne0\), reduction modulo 3 identifies its possible signed values with the nonzero vectors in \(\mathbb F_3^4\). Simultaneously replacing \((d,e)\) by \((-d,-e)\) preserves condition (*): \(r\) stays unchanged and \(\alpha,\beta\) change sign. It is therefore sufficient to check the 40 nonzero projective representatives whose first nonzero coordinate is 1. The value 2 in a representative denotes the signed difference −1.

For each such \(d\), form
\[
 t=-B_{S,O}^{\mathsf T}d.
\]
If \(t\) is outside the image of \(C_{O,S}\), every \(e\) has some \(\alpha_i\ne0\). If it is in the image, there is exactly one compatible \(e\). The checker computes \(r\) and \(\beta\) for that \(e\) and exhibits a site where \(r_i=1,\beta_i=0\).

The complete counts are:

| Exact check | Count |
|---|---:|
| Four-party cuts | 126 |
| Ternary inputs used to check injectivity | 10,206 |
| Nonzero projective binary difference classes | 5,040 |
| Classes with no compatible ternary difference | 2,970 |
| Classes with one compatible ternary difference | 2,070 |
| Compatible classes with at least one zero binary factor | 2,070 |
| Violations | 0 |

Among the compatible classes, the number of zero binary factors is distributed as follows: 418 classes have one, 761 have two, 601 have three, 249 have four, and 41 have five. `final_candidate_exact_certificate_v1.json` records the case and, when applicable, the compatible ternary difference and zero-factor sites for every one of the 5,040 classes.

The equal bra/ket entries have \(d=e=0\). Alternatively, since all amplitudes have squared modulus \(6^{-9}\), every diagonal reduced entry is
\[
 6^5\,6^{-9}=6^{-4}=1/1296.
\]
The full state has \(6^9\) coefficients of squared modulus \(6^{-9}\), so it is normalized. We have established
\[
 \operatorname{Tr}_{O}(|\Psi\rangle\langle\Psi|)=I_{6^4}/6^4
 \quad\text{for every }|S|=4.
\]
Taking a further partial trace proves the corresponding identity for every smaller set of parties. Hence \(|\Psi\rangle\) is an \(\mathrm{AME}(9,6)\) state. ∎

## 4. Reproduction

The dependency-free verifier requires only a standard Python 3 interpreter:

```sh
python round4/quantum_construction/verify_candidate_exact.py
```

It reads `final_candidate_v1.json`, validates dimensions, coefficient ranges and symmetries, enumerates every case above, and writes `final_candidate_exact_verification_v1.json` and `final_candidate_exact_certificate_v1.json`. It does not call the SAT solver. Its source implements the displayed criterion directly using integer sums, reduction modulo 2 and 3, and a dictionary of the 81 ternary images.

A second verifier, `round3/quantum/verify_mixed_graph.py`, independently enumerates all 81 ternary differences for each binary difference; it reports 2,070 compatible classes and zero violations for the same matrices. The additional independent amplitude and dense-Gram audits have completed successfully; their exact scope and results are recorded in Section 6 below.

For discovery, `global_mixed_sat.py` encoded all mixed-matrix and active ternary-phase variables with fixed \(G,C\), solved with Glucose4, and recovered the displayed matrices. It used 22,036 Boolean variables and 123,557 clauses for this instance. The solver found the witness after 87,409 conflicts, in 20.13 seconds in the discovery run. These search statistics play no role in the verification proof.

`final_candidate_sat_input_v1.cnf` is the exact SAT formula, with SHA256
`d0aaa60f30870a752cf5c06fcfb5befb6f132661d78c62cadb966c6ea7e2732a`.

## 5. Status and scope

The mathematical claim is existence of this specific \(\mathrm{AME}(9,6)\) state. Earlier searches that excluded fixed mixed matrices did not cover this new \(B\). The four matrices completely specify the construction, so no optimization output needs to be trusted.

A check of recent reports is separate from proof correctness. No claim of priority follows merely from a repository tag. The contemporaneous source and issue/PR audit is documented in `NOVELTY_AUDIT.md`; the present construction should be described as new only to the extent justified by that audit. Nothing has been posted to an issue, sent to another person, or published by this work.


## 6. Completed independent verification

The frozen candidate hash is shared by every check below. These checks were implemented independently from the SAT encoding.

1. **A separate small-matrix certificate.** `round4/ame_symbolic/SYMBOLIC_PROOF.md` derives the partial-trace formula from the amplitudes, including signed binary differences, complex conjugation, and both crossing terms of the mixed matrix. A standard-library generator produces 126 invertible four-row minors and zero-factor witnesses for all 80 nonzero signed binary differences at each cut. The separate checker performs integer matrix multiplication and does not invert a matrix or import another verifier. It certifies 822,420 ternary-cancellation and 4,140 binary-cancellation difference types.
2. **Complete amplitude phase table.** `round4/ame_direct/verify_full_phase.cpp` generates all 10,077,696 sixth-root exponents from the defining state polynomial. It checks all 826,560 nonzero difference types via first differences of that table. For all 4,140 types without a ternary zero factor, it also directly adds all 7,776 environments, for 32,192,640 terms. Every sum is exactly zero in the integer basis (1, eta), where eta = exp(pi*i/3) and eta² = eta − 1.
3. **Cross-check of the two exact routes.** The independently constructed symbolic and amplitude-based results agree for every one of the 126 cuts. The direct phase-table method uses the proved fact that environment-only quadratic terms cancel and common inside labels affect only an overall phase. It is not presented as an unrestricted black-box full trace of every entry of an arbitrary amplitude table.
4. **Negative control.** Feeding the previous score-4 near miss to the same direct program yields a nonzero environment sum with integer coefficients (−3888,7776), correctly rejecting that earlier state.
5. **Actual dense reduced matrices.** An independent NumPy implementation constructs the full tensor with nine physical axes of size six and local digit 3x+y. It directly contracts the seven cuts (0,1,3,8), (0,2,3,6), (1,2,3,4), (0,1,2,3), (5,6,7,8), (0,2,4,6), and (1,3,5,7). All seven pass. The maximum off-diagonal absolute value is 2.391758e-19; the maximum Frobenius error from I/1296 is 1.821269e-17. This is supplementary floating-point evidence for seven cuts; the integer certificate supplies the proof for all 126.
6. **Original declaration.** `round4/ame_scope/ORIGINAL_DECLARATION_SCOPE_AUDIT.md` verifies that the local basis identification, norm-one requirement, pure-state requirement, and all-permutation quantifier in `ExistsAME 9 6` match the construction.

The completed status is `round4/verification_status.json`. The historical frozen candidate record retains its discovery-time pending-audits label.

## 7. Source and priority audit, 22 September 2026

The exact FC declaration is in [the fixed repository file](https://github.com/google-deepmind/formal-conjectures/blob/62683d8562898ae70b021e1f8c78dfa8e6d86e96/FormalConjectures/OpenQuantumProblems/35.lean). The current source was fetched again at 12:36 UTC and agrees with that local file.

[Hontarenko and Życzkowski, arXiv:2609.11796v1](https://arxiv.org/abs/2609.11796v1), submitted 10 September 2026, displays (N,d)=(9,6) as existence unsettled in Figure 1. Its literature cutoff is 5 September, so this does not itself exclude later reports.

The fresh all-state FC AME issue/PR search returned 37 items. [PR 6008](https://github.com/google-deepmind/formal-conjectures/pull/6008) concerns (9,10); [PR 5561](https://github.com/google-deepmind/formal-conjectures/pull/5561) concerns (7,6), (7,10), and (12,5); the same-day [PR 6455](https://github.com/google-deepmind/formal-conjectures/pull/6455) concerns (11,10). The four issue comments on [PR 4198](https://github.com/google-deepmind/formal-conjectures/pull/4198) were recovered across all public timeline pages and did not contain a (9,6) solution.

The detailed bounded audit, retrieval failures, source dates, and metadata are in `round4/prior_ame/distribution/`. No same-parameter prior solution was found in those sources. This supports the report's **S-candidate** classification while leaving priority subject to further public review. No Lean kernel proof or external peer review is claimed, and no external submission has been made.

## 8. Reproduction from the supplied archive

From the archive root, the exact checks requiring only Python 3's standard library are:

```sh
python round4/quantum_construction/verify_candidate_exact.py
python round4/ame_symbolic/build_certificate.py
python round4/ame_symbolic/check_certificate.py
```

The complete phase-table and negative-control checks additionally require a C++17 `g++` compiler:

```sh
python round4/ame_direct/run_verification.py
python round4/ame_direct/negative_control.py
```

The supplementary dense check requires NumPy and several hundred MB of working memory:

```sh
python round4/ame_dense/independent_dense_audit.py
```

To reproduce discovery, install NumPy and python-sat with Glucose4 support and run `python round4/quantum_construction/global_mixed_sat.py 2 150000 glucose4` from the archive root. The numerical argument 150000 is a conflict budget. Solver timings and model choice may depend on the installed solver version; the saved integer witness and its verification are deterministic. The exact CNF and the earlier graph catalog used by this discovery script are included.
