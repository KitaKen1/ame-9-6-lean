"""Independent exact audit of the four matrices in the supplied AME(9,6) proof.

This script reads the displayed matrices directly from the archived Markdown.
It enumerates every nonzero pair of binary and ternary differences for every
four-party cut, without using the author's saved certificates or verifier.
"""

from collections import Counter
from itertools import combinations, product
from pathlib import Path
import json
import re
import sys


HERE = Path(__file__).resolve().parent
if len(sys.argv) > 2:
    raise SystemExit("Usage: python3 round76_ame_verify.py [AME_9_6_complete_proof_20260922.md]")
PROOF = (Path(sys.argv[1]) if len(sys.argv) == 2
         else HERE / "sources" / "AME_9_6_complete_proof_20260922.md")


def read_matrix(name, source):
    marker = name + r"=\begin{pmatrix}"
    assert source.count(marker) == 1, name
    body = source.split(marker, 1)[1].split(r"\end{pmatrix}", 1)[0]
    rows = []
    for match in re.finditer(r"[012](?:\s*&\s*[012]){8}", body):
        rows.append([int(item.strip()) for item in match.group().split("&")])
    assert len(rows) == 9 and all(len(row) == 9 for row in rows), name
    return rows


source = PROOF.read_text()
G, B, H, C = (read_matrix(name, source) for name in ("G", "B", "H", "C"))
for name, matrix, upper in (("G", G, 1), ("B", B, 2), ("H", H, 2), ("C", C, 2)):
    assert all(0 <= x <= upper for row in matrix for x in row), name
for name, matrix in (("G", G), ("H", H), ("C", C)):
    assert all(matrix[i][i] == 0 for i in range(9)), name
    assert all(matrix[i][j] == matrix[j][i] for i in range(9) for j in range(9)), name

all_ternary = list(product(range(3), repeat=4))
zero = (0, 0, 0, 0)
cuts = list(combinations(range(9), 4))
counts = Counter()
zero_factor_histogram = Counter()
violations = []
injectivity_failures = []

for S in cuts:
    O = tuple(i for i in range(9) if i not in S)
    c_images = {
        e: tuple(sum(C[i][j] * e[k] for k, j in enumerate(S)) % 3 for i in O)
        for e in all_ternary
    }
    if len(set(c_images.values())) != 81:
        injectivity_failures.append(S)
    counts["ternary_inputs_for_injectivity"] += 81

    for d in all_ternary:
        r = tuple(sum(G[i][j] * (d[k] != 0) for k, j in enumerate(S)) % 2 for i in O)
        mixed_alpha = tuple(sum(B[j][i] * d[k] for k, j in enumerate(S)) % 3 for i in O)
        h_beta = tuple(sum(H[i][j] * d[k] for k, j in enumerate(S)) % 3 for i in O)
        for e in all_ternary:
            if d == zero and e == zero:
                continue
            counts["nonzero_difference_types"] += 1
            alpha = tuple((c_images[e][k] + mixed_alpha[k]) % 3 for k in range(5))
            if any(alpha):
                counts["ternary_cancellations"] += 1
                continue
            counts["compatible_types"] += 1
            beta = tuple((h_beta[k] + sum(B[i][j] * e[l] for l, j in enumerate(S))) % 3
                         for k, i in enumerate(O))
            factors = [i for k, i in enumerate(O) if r[k] == 1 and beta[k] == 0]
            if factors:
                counts["binary_cancellations"] += 1
                zero_factor_histogram[len(factors)] += 1
            else:
                violations.append({"S": S, "d": d, "e": e, "r": r, "beta": beta})

assert len(cuts) == 126
assert not injectivity_failures, injectivity_failures[:3]
assert not violations, violations[:3]
assert counts["nonzero_difference_types"] == 826_560
assert counts["ternary_inputs_for_injectivity"] == 10_206
assert counts["ternary_cancellations"] == 822_420
assert counts["compatible_types"] == counts["binary_cancellations"] == 4_140
assert zero_factor_histogram == {1: 836, 2: 1522, 3: 1202, 4: 498, 5: 82}


# A separate exact amplitude check on actual reduced matrix entries catches
# transcription or sign mistakes in the factorized marginal formula.  Sixth
# roots of unity are represented in the integer basis (1, eta), eta^2=eta-1.
root_pairs = ((1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1))


def phase(x, y):
    binary = sum(G[i][j] * x[i] * x[j] for i in range(9) for j in range(i + 1, 9))
    ternary = sum(C[i][j] * y[i] * y[j] + H[i][j] * x[i] * x[j]
                  for i in range(9) for j in range(i + 1, 9))
    ternary += sum(B[i][j] * x[i] * y[j] for i in range(9) for j in range(9))
    return (3 * binary + 2 * ternary) % 6


def direct_entry(S, d, e):
    O = tuple(i for i in range(9) if i not in S)
    x, xp, y, yp = [0] * 9, [0] * 9, [0] * 9, [0] * 9
    for k, i in enumerate(S):
        x[i] = d[k] == 1
        xp[i] = d[k] == 2
        y[i] = e[k]
    total = [0, 0]
    for environment in product(range(6), repeat=5):
        for k, i in enumerate(O):
            x[i] = xp[i] = environment[k] // 3
            y[i] = yp[i] = environment[k] % 3
        a, b = root_pairs[(phase(x, y) - phase(xp, yp)) % 6]
        total[0] += a
        total[1] += b
    return tuple(total)


test_cut = (0, 1, 2, 3)
test_outside = tuple(i for i in range(9) if i not in test_cut)
compatible = None
incompatible = None
for test_d in all_ternary[1:]:
    for test_e in all_ternary:
        test_alpha = [sum(C[i][j] * test_e[k] + B[j][i] * test_d[k]
                          for k, j in enumerate(test_cut)) % 3 for i in test_outside]
        if not any(test_alpha) and compatible is None:
            compatible = (test_d, test_e)
        if any(test_alpha) and incompatible is None:
            incompatible = (test_d, test_e)
    if compatible and incompatible:
        break
assert compatible and incompatible
direct_checks = {
    "diagonal": direct_entry(test_cut, zero, zero),
    "ternary_only": direct_entry(test_cut, zero, (0, 0, 0, 1)),
    "incompatible_binary": direct_entry(test_cut, *incompatible),
    "compatible_binary": direct_entry(test_cut, *compatible),
}
assert direct_checks == {
    "diagonal": (7776, 0),
    "ternary_only": (0, 0),
    "incompatible_binary": (0, 0),
    "compatible_binary": (0, 0),
}, direct_checks

result = {
    "status": "PASS",
    "source": str(PROOF),
    "cuts": len(cuts),
    "counts": dict(sorted(counts.items())),
    "zero_factor_histogram": dict(sorted(zero_factor_histogram.items())),
    "violations": len(violations),
    "injectivity_failures": len(injectivity_failures),
    "direct_exact_amplitude_checks": direct_checks,
    "method": "All 126 cuts and all 3^8-1 signed difference types, exact integer arithmetic",
}
(HERE / "round76_ame_results.json").write_text(json.dumps(result, ensure_ascii=False, indent=2))
print(json.dumps(result, ensure_ascii=False))
