#!/usr/bin/env python3
"""
csrmatrix.py
----------------------------------------------------------
Generate a random integer CSR matrix A and vector x, then
dump them into dataset.h for use in Verilator/firmware tests.

* Default: 32 × 32, 10 % non‑zeros, int32 values in [‑4, 4]∖{0}
* Edit the constants below or pass --rows / --cols / --density.
"""

import argparse, textwrap, pathlib, numpy as np
import scipy.sparse as sp



HEADER_FILE = pathlib.Path("examples/sw/simple_system/common/dataset.h")
TEST_RESULTS_FILE = pathlib.Path("examples/sw/simple_system/hello_test/test_results.txt")
CTYPE       = "int32_t"         
VAL_LOW = -4
VAL_HIGH = 4



def random_csr(m: int, n: int, density: float, rng: np.random.Generator):
    nnz = max(1, int(m * n * density))
    rows = rng.integers(0, m, size=nnz, dtype=np.int32)
    cols = rng.integers(0, n, size=nnz, dtype=np.int32)
    vals = rng.integers(VAL_LOW, VAL_HIGH + 1, size=nnz, dtype=np.int32)
    vals[vals == 0] = 1  # make sure every non zero value is nonzero
    return sp.coo_matrix((vals, (rows, cols)), shape=(m, n)).tocsr()


def c_array(name: str, arr: np.ndarray, width: int = 78) -> str:
    body  = ", ".join(map(str, arr.tolist()))
    body  = textwrap.fill(body, width=width, subsequent_indent=" " * 4)
    return f"static const {CTYPE} {name}[{arr.size}] = {{ {body} }};"


def write_header(A: sp.csr_matrix, x: np.ndarray):
    guard = "DATASET_H_"
    m, n  = A.shape

    # --- new: column‑oriented view for fan‑out ----------------------------
    A_csc = A.tocsc()                   # ← used only for s_index / invcol_index
    # ---------------------------------------------------------------------

    lines = [
        f"#ifndef {guard}",
        f"#define {guard}",
        "",
        "",
        f"#define M {m}",
        f"#define N {n}",
        f"#define NNZ {A.nnz}",
        "",
        c_array("A_data",    A.data),
        "",
        c_array("A_indices", A.indices),
        "",
        c_array("A_indptr",  A.indptr),
        "",
        # --- new arrays ---------------------------------------------------
        c_array("invcol_index", A_csc.indices),
        "",
        c_array("s_index",      A_csc.indptr),
        # ------------------------------------------------------------------
        "",
        c_array("x",         x),
        "",
        f"#endif /* {guard} */",
        "",
    ]
    HEADER_FILE.write_text("\n".join(lines))
    print(f"[+] Wrote {HEADER_FILE}  (shape {m}×{n}, nnz={A.nnz})")


def main():
    ap = argparse.ArgumentParser(
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
        description="Create dataset.h containing a random CSR matrix + vector",
    )
    ap.add_argument("--rows",    type=int, default=8,  help="matrix rows")
    ap.add_argument("--cols",    type=int, default=8,  help="matrix cols")
    ap.add_argument("--density", type=float, default=0.10,
                    help="fraction of non‑zeros (0–1)")
    ap.add_argument("--seed",    type=int, default=None,
                    help="RNG seed (omit for random)")
    args = ap.parse_args()

    rng  = np.random.default_rng(args.seed)
    A    = random_csr(args.rows, args.cols, args.density, rng)
    x    = rng.integers(VAL_LOW, VAL_HIGH + 1, size=args.cols, dtype=np.int32)
    x[x == 0] = 1

    y = A @ x
    TEST_RESULTS_FILE.write_text("\n".join(str(val) for val in y))



    write_header(A, x)


if __name__ == "__main__":
    main()
