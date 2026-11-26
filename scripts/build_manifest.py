"""Build and verify SHA-256 MANIFEST.sha256 for VALIANT-HIER-CERT-1.0."""

from __future__ import annotations

import hashlib
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "MANIFEST.sha256"

INCLUDE_PATTERNS = [
    "README.md",
    "LICENSE",
    "CITATION.cff",
    "src/__init__.py",
    "src/valiant_hier_verifier.py",
    "lean/lean-toolchain",
    "lean/lakefile.toml",
    "lean/ValiantHierCert.lean",
    "scripts/generate_certificates.py",
    "scripts/generate_figures.py",
    "scripts/build_manifest.py",
    "tests/test_verifier.py",
    "paper/main.tex",
    "paper/references.bib",
    "paper/main.pdf",
]


def _tracked_files() -> list[pathlib.Path]:
    files: list[pathlib.Path] = []
    for rel in INCLUDE_PATTERNS:
        p = ROOT / rel
        if p.is_file():
            files.append(p)
    for d in ("certificates", "paper/figures"):
        dp = ROOT / d
        if dp.is_dir():
            for p in sorted(dp.iterdir()):
                if p.is_file() and p.suffix in {".json", ".pdf", ".png"}:
                    files.append(p)
    return sorted(set(files), key=lambda x: x.relative_to(ROOT).as_posix())


def _sha256(p: pathlib.Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main() -> int:
    check_mode = "--check" in sys.argv[1:]
    if check_mode:
        if not MANIFEST.is_file():
            print("MANIFEST.sha256 missing", file=sys.stderr)
            return 1
        lines = [ln.strip() for ln in MANIFEST.read_text(encoding="utf-8").splitlines() if ln.strip()]
        expected = {ln.split("  ", 1)[1]: ln.split("  ", 1)[0] for ln in lines}
        actual_files = _tracked_files()
        actual = {p.relative_to(ROOT).as_posix(): _sha256(p) for p in actual_files}
        if expected != actual:
            missing = set(expected) - set(actual)
            extra = set(actual) - set(expected)
            changed = {k for k in set(expected) & set(actual) if expected[k] != actual[k]}
            print(f"MANIFEST mismatch: missing={missing}, extra={extra}, changed={changed}", file=sys.stderr)
            return 1
        print(f"MANIFEST.sha256 OK: {len(actual)}/{len(actual)} files match.")
        return 0

    files = _tracked_files()
    out_lines = [f"{_sha256(p)}  {p.relative_to(ROOT).as_posix()}" for p in files]
    MANIFEST.write_text("\n".join(out_lines) + "\n", encoding="utf-8", newline="\n")
    print(f"Wrote MANIFEST.sha256 with {len(files)} files.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
