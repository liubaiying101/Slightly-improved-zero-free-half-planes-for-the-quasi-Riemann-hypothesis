#!/usr/bin/env python3
"""Build the minimal proof closure and strictly replay its public correspondence entry."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ENTRY = "RHZeroFreeExtension/CombinedPaperVerification.lean"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = ['rational_parameters', 'algebraic_parameters', 'balanced_signal_matching', 'rational_boundary', 'algebraic_boundary', 'boundary_order', 'original_family_bound', 'preliminary_family_bound', 'rational_family_bound', 'rational_hecke_nonzero', 'rational_dirichlet_nonzero', 'rational_zeta_nonzero', 'algebraic_family_bound', 'algebraic_hecke_nonzero', 'algebraic_dirichlet_nonzero', 'algebraic_zeta_nonzero', 'original_hecke_nonzero', 'original_dirichlet_nonzero', 'original_zeta_nonzero', 'rational_endpoint', 'algebraic_endpoint', 'scalar_obstruction']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command, log=None):
    return subprocess.run(command, cwd=ROOT, check=True, stdout=log,
                          stderr=subprocess.STDOUT if log else None)


def main():
    out = ROOT / "verification"
    out.mkdir(exist_ok=True)
    result = out / "result.json"
    result.unlink(missing_ok=True)
    foundation = json.loads((ROOT / "upstream/closure_manifest.json").read_text())
    if foundation["commit"] != "adc7f1241b42e322a6451854ab7e4b4c146bf78a":
        raise SystemExit("Unexpected upstream revision")
    for name, record in foundation["modules"].items():
        raw = (ROOT / record["path"]).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        if hashlib.sha256(raw).hexdigest() != record["sha256"] or blob != record["git_blob"]:
            raise SystemExit("Upstream source integrity failure: " + name)
    packages = json.loads((ROOT / "lake-manifest.json").read_text())
    for spec in packages["packages"]:
        if spec["type"] != "git":
            raise SystemExit("Unpinned package: " + spec["name"])
        path = ROOT / packages["packagesDir"] / spec["name"].strip("«»")
        head = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
        if head != spec["rev"]:
            raise SystemExit("Dependency revision mismatch: " + spec["name"])
    version = subprocess.check_output(["lake", "env", "lean", "--version"], cwd=ROOT, text=True).strip()
    pin = (ROOT / "lean-toolchain").read_text().strip()
    if not re.search(r"Lean \(version " + re.escape(pin.rsplit(":v", 1)[-1]) + r"[,\s]", version):
        raise SystemExit("Lean version does not match lean-toolchain")
    paths = sorted(p for p in ROOT.rglob("*.lean") if ".lake" not in p.relative_to(ROOT).parts)
    paths += [ROOT / n for n in ["lean-toolchain", "lake-manifest.json", "verify.py",
              "upstream/closure_manifest.json", "vendor/LICENSE"]]
    paths += sorted((ROOT / "upstream").glob("*.patch"))
    hashes = {str(p.relative_to(ROOT)): sha(p) for p in paths}
    print("Building the complete import closure...", flush=True)
    with (out / "build.log").open("w") as log:
        run(["lake", "build", "RHZeroFreeExtension.CombinedPaperVerification"], log)
    print("Replaying the 22 correspondence theorems with --trust=0...", flush=True)
    command = ["lake", "env", "lean", "--trust=0", "-DautoImplicit=false",
               "-DwarningAsError=true", ENTRY]
    with (out / "kernel.log").open("w") as log:
        run(command, log)
    diagnostics = (out / "kernel.log").read_text()
    if re.search(r"error:|sorryAx|declaration uses .sorry.", diagnostics):
        raise SystemExit("Rejected kernel diagnostics")
    axioms = {}
    for name, deps in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", diagnostics, re.S):
        deps = {x.strip() for x in deps.split(",") if x.strip()}
        if not deps <= ALLOWED:
            raise SystemExit("Unexpected axiom in " + name)
        axioms[name] = sorted(deps)
    for name in EXPECTED:
        if "CombinedPaper." + name not in axioms:
            raise SystemExit("Missing axiom report: " + name)
    if any(sha(ROOT / name) != expected for name, expected in hashes.items()):
        raise SystemExit("Source changed during replay")
    record = {
        "status": "PASS: public analytic conclusions and correspondence entry",
        "scope_limit": "Not a literal verification of every manuscript statement or the full broad optimality claim.",
        "toolchain": pin, "runtime_version": version, "command": command,
        "axioms": axioms, "source_hashes": hashes,
        "kernel_log_sha256": sha(out / "kernel.log"),
    }
    result.write_text(json.dumps(record, indent=2) + "\n")
    print(record["status"])
    print("All 22 expected theorems use only standard Lean axioms.")
    print(record["scope_limit"])


if __name__ == "__main__":
    main()
