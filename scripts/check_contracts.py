"""Typecheck the release interface and confirm that seven mathematical changes fail."""

from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
CASES = (
    ("from_fourth_order", "HasGaussianGammaLaw μ F G p", "HasGaussianGammaLaw μ G F p"),
    ("from_exact_averages", "PreservesAt F G q", "True"),
    ("affine_chart_formulas", "B.toBasis (-l)", "B.toBasis l"),
    ("product_log_partition", "↔ admissible l v", "↔ admissible l (-v)"),
    ("gamma_transform_and_domain", "(r/(r-t))^a", "(r/(r+t))^a"),
    ("global_product_averages", "a+b=x+y", "a+b=x-y"),
    ("fisher_axis_coordinates", "= sExp (-l) x", "= sExp l x"),
)


def check_lean(path: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["lake", "env", "lean", str(path)], cwd=ROOT,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
    )


def main() -> None:
    solution = (ROOT / "Solution.lean").read_text()
    with tempfile.TemporaryDirectory() as temporary:
        control = Path(temporary) / "Control.lean"
        control.write_text(solution)
        result = check_lean(control)
        if result.returncode:
            raise RuntimeError(f"The unmodified interface failed.\n{result.stdout}")
        print("PASS unmodified Solution")

        for name, old, new in CASES:
            start = solution.index(f"theorem {name} ")
            stop = solution.index(" := by", start)
            statement = solution[start:stop]
            if statement.count(old) != 1:
                raise ValueError(f"Expected one matching expression in {name}")
            mutated = statement.replace(old, new)
            control.write_text(solution[:start] + mutated + solution[stop:])
            result = check_lean(control)
            if result.returncode == 0:
                raise AssertionError(f"Accepted corrupted declaration {name}")
            # The mutation must fail on the affected proof after the changed statement.
            first_line = solution.count("\n", 0, stop) + 1
            end = solution.find("\n\n", stop)
            last_line = solution.count("\n", 0, end) + 1
            expected = any(f"Control.lean:{line}:" in result.stdout
                           for line in range(first_line, last_line + 1))
            if not expected or "error" not in result.stdout:
                raise RuntimeError(f"Unexpected failure for {name}.\n{result.stdout}")
            print(f"PASS rejected corrupted {name}")


if __name__ == "__main__":
    main()
