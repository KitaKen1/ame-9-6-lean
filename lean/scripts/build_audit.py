"""Build and audit the complete FC existence proof, preserving source hashes."""
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess
import time
from types import SimpleNamespace

root = Path(__file__).resolve().parents[1]
start = time.monotonic()
process = subprocess.Popen(["lake", "--wfail", "build", "AME96", "AME96.Audit"],
                           cwd=root, text=True, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT)
lines = []
with (root / "evidence/build.log").open("w") as log:
    for line in process.stdout:
        lines.append(line)
        log.write(line)
        log.flush()
        print(line, end="", flush=True)
run = SimpleNamespace(returncode=process.wait(), stdout="".join(lines))
elapsed = time.monotonic() - start
axioms = {}
for name, values in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", run.stdout):
    axioms[name] = [v.strip() for v in values.split(",") if v.strip()]
allowed = {"propext", "Classical.choice", "Quot.sound"}
required = ["AME96.allCuts_cancels", "AME96.allCuts_complete", "AME96.allCuts_partition",
            "AME96.everyPartition_cancels", "AME96.mixedPhase_environment_sum",
            "AME96.reduction_eq", "AME96.state_normalized", "AME96.state_isAME",
            "AME96.exists_ame_9_6", "AME96.ame_9_6_answer_true"]
audit_ok = all(name in axioms and set(axioms[name]) <= allowed for name in required)
files = [*sorted((root / "AME96").glob("*.lean")), root / "AME96.lean",
         root / "lakefile.toml", root / "lake-manifest.json", root / "lean-toolchain",
         *sorted((root / "scripts").glob("*.py"))]
result = {
    "status": "PASS" if run.returncode == 0 and audit_ok else "FAIL",
    "scope": "Full explicit AME(9,6) existence proof in the pinned FC definition",
    "ame_existence_proved": run.returncode == 0 and audit_ok,
    "all_126_cuts_proved": run.returncode == 0 and audit_ok,
    "partial_trace_factorization_proved": run.returncode == 0 and audit_ok,
    "checked_cuts": 126,
    "nonzero_difference_types_covered": 826560,
    "certificate_nonzero_binary_differences": 10080,
    "unconditional_theorem": "AME96.exists_ame_9_6",
    "formal_target_theorem": "AME96.ame_9_6_answer_true",
    "checked_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "command": "lake --wfail build AME96 AME96.Audit",
    "exit_code": run.returncode,
    "elapsed_seconds": round(elapsed, 3),
    "timing_note": "This build may reuse compiled modules; elapsed time is not pure kernel-checking time.",
    "first_cut_timing_note": "Historical first successful Lake module build; includes module loading and host contention.",
    "first_cut_initial_module_build_seconds_reported_by_lake": 33,
    "lean_version": (root / "lean-toolchain").read_text().strip(),
    "fc_commit": "2a46c7bd74505b85f4967475bb733ded0ef8d348",
    "mathlib_commit": "0df444a360eaa60ab8c11dca51a86af692955474",
    "axiom_audit_passed": audit_ok,
    "axioms": axioms,
    "source_sha256": {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in files},
}
(root / "evidence/build_results.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
print(json.dumps({k: result[k] for k in ["status", "exit_code", "elapsed_seconds",
                                      "axiom_audit_passed", "ame_existence_proved"]}))
raise SystemExit(0 if result["status"] == "PASS" else 1)
