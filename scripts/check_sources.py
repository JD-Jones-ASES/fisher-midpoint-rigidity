"""Audit tracked release sources and run Lean's axiom report for the public theorems."""

import json
from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    paths = subprocess.check_output(
        ["git", "ls-files", "-z", "--", "*.lean"], cwd=ROOT,
    ).decode().split("\0")
    sources = [ROOT / path for path in paths if path]
    for path in sources:
        source = path.read_text()
        if path.is_symlink() or source.splitlines()[0] != "module" or len(source.splitlines()) > 10_000:
            raise ValueError(f"Invalid source layout in {path.name}")
        if path.name != "Challenge.lean" and re.search(r"\b(sorry|admit|axiom)\b", source):
            raise ValueError(f"Unexpected proof placeholder or axiom in {path.name}")

    challenge = (ROOT / "Challenge.lean").read_text()
    config = json.loads((ROOT / "comparator.json").read_text())
    names = config["theorem_names"]
    if len(names) != len(set(names)) or challenge.count("  sorry\n") != len(names):
        raise ValueError("The statement holes and compared names disagree")
    if len(challenge.encode()) > 100 * 1024 or len(challenge.splitlines()) > 1000:
        raise ValueError("Challenge exceeds Palomar's source limits")

    public_names = re.findall(r"^(?:abbrev|def|structure|theorem) (\w+)", challenge, re.MULTILINE)
    subprocess.run(
        ["lake", "env", "lean", "--run", "scripts/compare_interface.lean", *names],
        cwd=ROOT, check=True,
    )
    print(f"PASS recursive declaration comparison for {len(names)} theorems")
    signatures = "".join(f"#check @FisherMidpoint.{name}\n" for name in public_names)
    with tempfile.TemporaryDirectory() as temporary:
        signature_file = Path(temporary) / "Signatures.lean"
        reports = []
        for module in ("Challenge", "Solution"):
            signature_file.write_text(
                f"import {module}\nset_option pp.universes true\nset_option pp.fullNames true\n" + signatures
            )
            reports.append(subprocess.check_output(
                ["lake", "env", "lean", str(signature_file)], cwd=ROOT, text=True,
            ))
        if reports[0] != reports[1]:
            raise ValueError("The independently elaborated public declaration signatures differ")
        print(f"PASS matching signatures for {len(public_names)} public declarations")
        report = Path(temporary) / "Axioms.lean"
        report.write_text("import Solution\n" + "".join(f"#print axioms {n}\n" for n in names))
        out = subprocess.check_output(["lake", "env", "lean", str(report)], cwd=ROOT, text=True)
    permitted = set(config["permitted_axioms"])
    if permitted != {"propext", "Classical.choice", "Quot.sound"}:
        raise ValueError("Unexpected permitted-axiom configuration")
    for name in names:
        match = re.search(rf"'{re.escape(name)}' depends on axioms: \[([^\]]*)\]", out)
        if not match and f"'{name}' does not depend on any axioms" not in out:
            raise ValueError(f"Missing axiom report for {name}.\n{out}")
        used = set(a.strip() for a in match[1].split(",") if a.strip()) if match else set()
        if used - permitted:
            raise ValueError(f"Unexpected axioms for {name}: {used - permitted}")
    print(f"PASS {len(sources)} Lean sources and the axiom closure of {len(names)} compared theorems")


if __name__ == "__main__":
    main()
