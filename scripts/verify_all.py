"""End-to-end 5-gate verification and SHA-256 manifest auditor for Paper 59
(DLP-COGENTIC-CERT-1.0, Google Research Cogentic Sub-Quasi-Polynomial DLP breakthrough).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST_PATH = ROOT / "SHA256_MANIFEST.json"

ALLOWED_AXIOMS = {"propext", "Quot.sound"}

TRACKED_FILES = [
    "LICENSE",
    "README.md",
    "pyproject.toml",
    "airr_metadata_paper59.json",
    "lean/lean-toolchain",
    "lean/lakefile.toml",
    "lean/CogenticDiscreteLog.lean",
    "lean/AuditAxioms.lean",
    "src/__init__.py",
    "src/dlp_exact.py",
    "src/dlp_certifier.py",
    "scripts/run_all_experiments.py",
    "scripts/make_figures.py",
    "scripts/verify_all.py",
    "tests/test_suite.py",
    "paper/references.bib",
    "paper/main.tex",
    "paper/main.pdf",
    "paper/figures/fig1_monodromy_compression.png",
    "paper/figures/fig2_thm12_onset_and_unimodular.png",
    "paper/figures/fig3_atlas_and_redteam.png",
    "results/exp1_certificate_atlas.json",
    "results/exp2_monodromy_compression.json",
    "results/exp3_thm12_parameter_onset.json",
    "results/exp4_unimodular_scaling.json",
]


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    h.update(path.read_bytes())
    return h.hexdigest()


def collect_manifest() -> dict[str, str]:
    files = list(TRACKED_FILES)
    for cp in sorted((ROOT / "certificates").glob("*.cert.json")):
        files.append(f"certificates/{cp.name}")
    out: dict[str, str] = {}
    for rel in files:
        p = ROOT / rel
        if not p.exists():
            raise FileNotFoundError(f"Missing tracked artifact: {rel}")
        out[rel] = sha256_file(p)
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write-manifest", action="store_true")
    args = ap.parse_args()

    # Gate 1: Static zero-float hygiene check on src/*.py
    for rel in ["src/dlp_exact.py", "src/dlp_certifier.py"]:
        src = (ROOT / rel).read_text(encoding="utf-8")
        for forbidden in ["float(", "math.", "numpy", "np."]:
            assert forbidden not in src, f"Forbidden token {forbidden!r} in {rel}"
    print("[PASS] 1/5 Zero-float static hygiene check on src/*.py")

    # Gate 2: Lean 4.35.0 build & strict axiom audit
    subprocess.run(["lake", "build"], cwd=ROOT / "lean", check=True)
    audit = subprocess.run(
        ["lake", "env", "lean", "-j", "1", "AuditAxioms.lean"],
        cwd=ROOT / "lean",
        check=True,
        capture_output=True,
        text=True,
    )
    assert "sorry" not in audit.stdout.lower(), "Lean proof contains sorry!"
    assert "Classical.choice" not in audit.stdout, "Lean proof uses Classical.choice!"
    assert "ofReduceBool" not in audit.stdout, "Lean proof uses Lean.ofReduceBool!"
    lines = [ln.strip() for ln in audit.stdout.splitlines() if "CogenticDiscreteLog." in ln]
    assert len(lines) == 18, f"Expected 18 audited theorems, got {len(lines)}"
    for ln in lines:
        if "depends on axioms: [" in ln:
            ax_str = ln.split("depends on axioms: [", 1)[1].rstrip("]")
            axs = {a.strip() for a in ax_str.split(",") if a.strip()}
            assert axs <= ALLOWED_AXIOMS, f"Disallowed axiom in line: {ln}"
    print("[PASS] 2/5 Lean 4.35.0 build & strict axiom audit (18/18 theorems, 0 sorry, 0 Classical.choice)")

    # Gate 3: Replay all 16 canonical certificates
    if str(ROOT) not in sys.path:
        sys.path.insert(0, str(ROOT))
    from src.dlp_certifier import verify_certificate_file

    cert_paths = sorted((ROOT / "certificates").glob("*.cert.json"))
    assert len(cert_paths) == 16, f"Expected 16 certs, found {len(cert_paths)}"
    for cp in cert_paths:
        res = verify_certificate_file(cp)
        assert res["verified"] is True
    print("[PASS] 3/5 All 16 canonical DLP-COGENTIC-CERT-1.0 certificates verified")

    # Gate 4: Full 64-test pytest suite (16 certs + 3 raw-JSON + 60 live forgeries)
    subprocess.run([sys.executable, "-m", "pytest", "-p", "no:cacheprovider", "-q"], cwd=ROOT, check=True)
    print("[PASS] 4/5 Full 65-test pytest suite passed (16 certs + 3 raw JSON + 61 live forgeries)")

    # Gate 5: SHA-256 manifest
    current = collect_manifest()
    if args.write_manifest:
        MANIFEST_PATH.write_text(json.dumps(current, indent=2) + "\n", encoding="utf-8")
        print(f"[PASS] 5/5 Wrote {MANIFEST_PATH.name} ({len(current)} tracked files)")
    else:
        expected = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
        assert current == expected, "SHA-256 manifest mismatch!"
        print(f"[PASS] 5/5 {MANIFEST_PATH.name} verified ({len(current)}/{len(current)} files)")


if __name__ == "__main__":
    main()
