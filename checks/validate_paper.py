#!/usr/bin/env python3
"""Clean-build and audit this standalone Lean package; diagnostics are optional.

Requires Python 3.10+, Git and the pinned Lean toolchain via elan.
Every project input is resolved inside this repository. No Git commit,
paper source, NumPy, or sibling checkout is required.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
ENTRY_POINT = "CoefficientwiseRigidity.manuscriptMainTheorems : ManuscriptMainTheorems"


def project_files():
    """The public source inventory, excluding downloads and generated output."""
    files = list(ROOT.glob("*.lean"))
    files += list((ROOT / "CoefficientwiseRigidity").glob("*.lean"))
    files += list((ROOT / "checks").glob("*.py"))
    files += list(ROOT.glob("*.md"))
    files += [ROOT / name for name in (
        "lean-toolchain", "lakefile.toml", "lake-manifest.json",
        "MANUSCRIPT.json", "LICENSE", ".gitignore", ".gitattributes")]
    files += list((ROOT / ".github" / "workflows").glob("*.yml"))
    return sorted(files)


def preflight(files):
    for path in files:
        if path.is_symlink() or not path.is_file():
            raise RuntimeError(f"Public source is not a regular file: {path.relative_to(ROOT)}")
        data = path.read_text()
        if not data.endswith("\n"):
            raise RuntimeError(f"Missing final newline: {path.relative_to(ROOT)}")
        if re.search(r"[ \t]+$", data, re.MULTILINE):
            raise RuntimeError(f"Trailing whitespace: {path.relative_to(ROOT)}")
        if re.search(r"/(?:Users|home)/[A-Za-z]", data):
            raise RuntimeError(f"External research path: {path.relative_to(ROOT)}")
    for path in files:
        if path.suffix != ".lean":
            continue
        for imported in re.findall(r"^import\s+([\w.]+)", path.read_text(), re.MULTILINE):
            if imported.split(".")[0] in {"CoefficientwiseRigidity", "PaperAudit"}:
                local = ROOT / (imported.replace(".", "/") + ".lean")
                if not local.is_file():
                    raise RuntimeError(f"Missing project module {imported}")
    config = (ROOT / "lakefile.toml").read_text()
    if re.search(r"^\s*path\s*=", config, re.MULTILINE):
        raise RuntimeError("Lake configuration must not use a local path dependency")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        if package["type"] != "git" or not re.fullmatch(r"[0-9a-f]{40}", package["rev"]):
            raise RuntimeError(f"Dependency is not pinned to a Git revision: {package['name']}")
    if shutil.which("lake") is None:
        raise RuntimeError("lake is unavailable; install elan and add its bin directory to PATH")
    if shutil.which("git") is None:
        raise RuntimeError("Git is required to obtain and check the pinned dependencies")
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--clean", action="store_true",
                        help="Remove this project's build products; keep dependency caches.")
    parser.add_argument("--lean-only", action="store_true",
                        help="Skip the optional independent finite diagnostics.")
    parser.add_argument("--output-dir", type=Path, default=ROOT / "validation",
                        help="Directory for the receipt and command logs (default: validation/).")
    args = parser.parse_args()
    files = project_files()
    manifest = preflight(files)
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    records = []

    def run(name, command):
        log = output / (name + ".log")
        print(f"Running {name} ...", flush=True)
        with log.open("w") as stream:
            result = subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
        records.append({"name": name, "command": command, "cwd": ".",
                        "exit_code": result.returncode})
        text = log.read_text()
        if result.returncode:
            raise RuntimeError(f"{name} failed; inspect {log}")
        if name in {"build", "axiom-audit"} and re.search(r"\bwarning:", text):
            raise RuntimeError(f"{name} emitted a warning; inspect {log}")
        print(f"{name}: PASS", flush=True)
        return text

    if args.clean:
        run("clean", ["lake", "clean", manifest["name"]])
    lean_version = run("lean-version", ["lake", "env", "lean", "--version"]).strip()
    run("build", ["lake", "build"])
    # Run the audit again explicitly, even when Lake can reuse a compiled target.
    audit_text = run("axiom-audit", ["lake", "env", "lean", "PaperAudit.lean"])
    audit = re.search(r"Axiom audit PASS: (\d+) project declarations, (\d+) theorem declarations",
                      audit_text)
    if not audit or "CoefficientwiseRigidity.manuscriptMainTheorems" not in audit_text:
        raise RuntimeError(f"Missing publication entry point or audit result; inspect {output}")

    dependencies = {}
    for package in manifest["packages"]:
        checkout = ROOT / manifest["packagesDir"] / package["name"]
        actual = subprocess.check_output(
            ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
        if actual != package["rev"]:
            raise RuntimeError(f"Dependency revision mismatch: {package['name']}")
        dependencies[package["name"]] = actual

    computational = {}
    if not args.lean_only:
        for name in ["check_paper_alignment", "check_main_c"]:
            result = json.loads(run(name, [sys.executable, str(ROOT / "checks" / (name + ".py"))]))
            if result.get("status") != "COMPUTATIONAL" or result.get("result") != "PASS":
                raise RuntimeError(f"Diagnostic did not pass: {name}")
            computational[name] = result

    revision_result = subprocess.run(
        ["git", "rev-parse", "--verify", "HEAD"], cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    revision = revision_result.stdout.strip() if revision_result.returncode == 0 else None
    receipt = {
        "status": "VERIFIED",
        "evidence": "Lean kernel checked; finite diagnostics separately COMPUTATIONAL",
        "validated_at_utc": datetime.now(timezone.utc).isoformat(),
        "git_revision": revision,
        "entry_point": ENTRY_POINT,
        "scope": "Main Theorems A-C; auxiliary exclusions in FORMALIZATION.md",
        "clean_project_rebuild": args.clean,
        "dependency_build_cache": "May be reused; exact source revisions checked against the manifest.",
        "lean_version": lean_version,
        "dependency_revisions": dependencies,
        "audit": {"safe_declarations": int(audit[1]), "theorem_declarations": int(audit[2]),
                  "allowed_axioms": ALLOWED_AXIOMS, "warnings": 0},
        "commands": records,
        "computational": computational,
        "manuscript": json.loads((ROOT / "MANUSCRIPT.json").read_text()),
        "source_sha256": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in files},
    }
    receipt_path = output / "VALIDATION.json"
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"PASS: {receipt_path}", flush=True)


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
