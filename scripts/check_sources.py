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

    with tempfile.TemporaryDirectory() as temporary:
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
