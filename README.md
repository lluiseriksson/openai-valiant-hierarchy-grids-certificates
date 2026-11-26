# VALIANT-HIER-CERT-1.0: Constructive Graph State-Sum, Isoperimetric, and Dyadic-Placement Certificates for Separating Valiant's Algebraic Hierarchy

**Author:** Lluis Eriksson (`lluis@airr.science`)  
**Schema:** `VALIANT-HIER-CERT-1.0`  
**Target Preprint:** OpenAI, *"Paths, trees and grids separate Valiant's hierarchy"* (`OAI:Paths-trees-and-grids-separate-Valiants-hierarchy-November-24-2026`, unrefereed preprint, November 24, 2026).

## Overview
This repository provides an independently reproducible, zero-floating-point Python verification engine (`src/valiant_hier_verifier.py`), a constructive Lean 4.35.0 kernel (`lean/ValiantHierCert.lean`, 18 constructive theorems, 0 `sorry`, 0 custom axioms, 0 `Classical.choice`, 0 warnings), 16 canonical JSON certificates (`certificates/C01..C16`), 69 unit and adversarial forgery tests (`tests/test_verifier.py`), 3 publication figures, and a 4-page LaTeX/PDF companion paper (`paper/main.pdf`).

## Quick Reproduction
```bash
cd lean && lake build && cd ..
python -m src.valiant_hier_verifier certificates/
pytest -q
python scripts/build_manifest.py --check
```

## Licenses & Disclosure
- Manuscript & figures: `CC-BY-4.0`
- Code, Lean proofs & certificates: `MIT`
- Produced with Google Antigravity assistance; independently compiled, verified, and reviewed by Lluis Eriksson.
